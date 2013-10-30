#! /usr/bin/env python
# -*- encoding: utf-8 -*-

# Compile effective_tld_names.dat into an efficient data structure
# for lookups.  Currently only handles C; see generateEffectiveTLDs.php
# for the Perl and PHP data structures.
#
# The DFA generation algorithm is roughly Algorithm 1 from
# "Incremental Construction of Minimal Acyclic Finite-State Automata"
# <http://aclweb.org/anthology/J/J00/J00-1002.pdf>.  The serialized
# representation resembles that described in "Tightly Packed Tries"
# <http://aclweb.org/anthology/W/W09/W09-1505.pdf>, with further
# space and speed optimizations.
#
# Licensed under the Apache License, Version 2.0; you may not use this file
# except in compliance with the License. You may obtain a copy of the License
# at: http://www.apache.org/licenses/LICENSE-2.0
#
# Zack Weinberg, 2013-10-23, zackw@panix.com

import cStringIO
import errno
import numbers
import os
import string
import sys
import textwrap

VERBOSE = False

#
# DFA compression and serialization.
#

class Opcode(object):
    """Low-level serialized representation of the DFA.

       Abstractly, there are two kinds of states: _branch_ states,
       which make an N-way choice among valid possibilities for the
       next character, and _literal_ states, which require the next N
       characters to match a string literal.  (Even more abstractly, a
       literal state is just an optimized representation of a chain of
       1-way branch states.)  Furthermore, any state can be tagged
       with a "stop code", which indicates that the automaton can stop
       successfully _before_ consuming any characters associated with
       that state, and the result of the match.

       Both types of state, again abstractly, have three fields in
       their storage representation:

           opcode | data | out-edges

       The opcode is one or two bytes long; it defines the operation
       to perform next and the sizes of the 'data' and 'out-edges'
       fields.  Opcodes have a fairly elaborate format, in order to
       save space.  "Normal" opcodes are broken into four bitfields:

           bit 76 5 43 210
               SS O WW LLL

       The S bits are a _stop code_, indicating whether or not the
       automaton can stop successfully _just before_ processing any
       characters associated with this state, and if so, with what
       result.  There are three possibilities for the SS bits:

           00  nonstop
           01  stop (normal)
           10  stop (all)

       The fourth possible bit pattern indicates a "special" opcode;
       see below.

       The O bit indicates whether the state is a branch or a literal:

            0  literal
            1  branch

       This determines the overall format of the 'data' and
       'out-edges' fields of the state.  For literal states, 'data' is
       an ASCII string to match (whose length is set by the L bits,
       see below) starting from the current position.  Immediately
       after the data is one out-edge entry, which indicates the
       next state upon a successful match.  For branch states, 'data'
       is instead a sorted vector of L characters, any of which is an
       acceptable match for the very next character, and 'out-edges' is
       a vector of L out-edge entries, giving the next state for each
       possibility.  This vector may be compacted as described below.

       The W bits indicate the width of the out-edge entries for this
       opcode:

           00  compact
           01  1 byte per entry
           10  2 bytes per entry
           11  3 bytes per entry

        The "compact" option's meaning depends on the type of
        state.  For literal states, it means there is no out-edge
        field at all; the subsequent state on a successful match
        immediately follows the end of the data field.  For branch
        states, it means that there is a _single_ 1-byte out-edge
        field, which indicates the subsequent state for _any_
        successful match in this state.  (This happens more often than
        you'd think.)

        Each out-edge entry is a big-endian, unsigned binary number
        giving the distance in bytes (within the DFA serialization)
        from the _end_ of the current state to the _beginning_ of the
        next one.  However, if the next state is a full stop -- that
        is, an accepting state with no out-edges of its own -- then
        it is represented with a special code in the edge vector:

            0   normal
            1   all
            2   this

         There is no stop code for a "this" match because "this"
         matches cannot be a prefix of any other match.  To make space
         for these special codes, all other out-edge values are 3 +
         actual displacement.  Note that a compact literal's out-edge
         field indicates zero _displacement_, not zero as in normal
         match.

         Finally, the L bits give the length of the data field (and
         the out-edge field, for non-compact branches).  They form a
         3-bit unsigned binary number, which is the length minus one
         for literal states, and the length minus two for branch
         states (because it doesn't make sense to have zero characters
         of literal data, or zero or one characters of branch data).
         If the value is 111, for either type of state, it means that
         an additional 'length' byte immediately follows; in that case
         the value in the length byte is the length without any
         offsets (this means there are some redundant encodings for
         short lengths, but the gain in simplicity is worth it, and we
         have plenty of headroom at the high end).

         "Special" opcodes compact an entire state into a single
         opcode byte.  All special opcodes have their highest two bits
         set:

             bit 76 54 3210
                 11 dd dddd

         At present, two types of special opcode are defined:

             * If DDDDDD is 0x0D, 0x0E, 0x10 .. 0x19, or 0x21 .. 0x3A,
               then this is a hyper-compact literal state, whose text
               is the single ASCII character DDDDDD + 32, and whose
               successor state immediately follows.

             * If DDDDDD is 0, 1, or 2, this is a full-stop state
               whose match type is normal, all, or this, respectively.
               Normally such states are packed into their
               predecessors' edge tables, but if a state of this type
               is the successor for a (hyper-)compact literal state,
               there is no edge table to pack it into.

          All other special-opcode bit patterns are reserved for
          future definition.
    """

    # Stop codes, corresponding to the three types of rule.
    # The three types of rule receive a rather confusing definition in
    # the spec, but it amounts to the following: if a rule with type X
    # is the longest match for a domain name, then the registered
    # domain is:
    STOP_NORMAL  = 0x00  # the current match plus one label
    STOP_ALL     = 0x01  # the current match plus two labels
    STOP_THIS    = 0x02  # the current match
    STOP_OFFSET  = 0x03 # subtract this from out-edges >= this to get an offset

    # Stop codes can also appear as the high bits of a regular state's
    # opcode.  This happens when one rule is a proper prefix of
    # another rule.  It is impossible for this to happen for THIS matches,
    # so that bit pattern is recycled to tag "special" opcodes.
    TAG_MASK     = 0xC0
    TAG_SHIFT    = 6
    TAG_NONE     = 0x00
    TAG_NORMAL_S = 0x01
    TAG_ALL_S    = 0x02
    TAG_SPECIAL  = 0x03

    # The next bit down encodes whether this is a "literal" or a
    # "branch" operation.
    OP_MASK  = 0x20
    OP_BRA   = 0x20
    OP_LIT   = 0x00

    # The next two bits down tell you the width of the displacement
    # fields in this DFA state.
    WIDTH_MASK = 0x18
    WIDTH_SHIFT = 3

    # The bottom three bits of an opcode encode the number of jump
    # table entries (for "branch") or the length of the text (for
    # "literal").
    LENGTH_MASK        = 0x07
    LENGTH_EXTENDED    = 0x07

    LENGTH_OFFSET_LIT  = 1
    LENGTH_OFFSET_BRA  = 2

    LENGTH_MAX_LIT     = 7
    LENGTH_MAX_BRA     = 8

    @classmethod
    def encode_normal(cls, stop, main, width, length):
        """Encode STOP, MAIN, WIDTH, and LENGTH into a one- or
           two-byte opcode.  Note that the returned string is backward,
           because the entire DFA will be reversed when we're done
           generating it."""
        if stop is None: stop = 0
        elif stop == cls.STOP_NORMAL: stop = cls.TAG_NORMAL_S << cls.TAG_SHIFT
        elif stop == cls.STOP_ALL:    stop = cls.TAG_ALL_S    << cls.TAG_SHIFT
        else:
            raise RuntimeError("bad stop value {!r}".format(stop))

        assert main in (cls.OP_BRA, cls.OP_LIT)
        assert 0 <= width <= 3
        if main == cls.OP_BRA:
            lmax = cls.LENGTH_MAX_BRA
            loff = cls.LENGTH_OFFSET_BRA
        else:
            lmax = cls.LENGTH_MAX_LIT
            loff = cls.LENGTH_OFFSET_LIT

        opbase = stop | main | (width << cls.WIDTH_SHIFT)

        if length <= lmax:
            return chr(opbase | (length - loff))
        else:
            return chr(length) + chr(opbase | cls.LENGTH_EXTENDED)

    @classmethod
    def encode_special(cls, value):
        if isinstance(value, numbers.Number):
            assert cls.is_stop_code(value)
            return chr(cls.TAG_SPECIAL << cls.TAG_SHIFT | value)
        else:
            assert len(value) == 1
            if value not in "-.0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ":
                raise RuntimeError("cannot put {!r} in a hypercompact literal"
                                   .format(value))
            return chr(cls.TAG_SPECIAL << cls.TAG_SHIFT | (ord(value) - 32))

    @staticmethod
    def encode_offset(delta):
        """Encode the distance DELTA in the minimum possible number of
           bytes, and return it.  Again, the returned string is backward."""
        if delta < 256:
            return chr(delta)
        elif delta < 256*256:
            return (chr((delta & 0x00FF)     ) +
                    chr((delta & 0xFF00) >> 8))
        else:
            assert delta < 256*256*256
            return (chr((delta & 0x0000FF)      ) +
                    chr((delta & 0x00FF00) >>  8) +
                    chr((delta & 0xFF0000) >> 16))

    @classmethod
    def enc_lit_offset(cls, to, fro):
        """Encode the absolute distance from FRO to TO (both of which
           are byte counts, with FRO >= TO) in the minimum number of
           bytes for a LITERAL state. Return an appropriately encoded
           string (yep, backward)."""
        if to == fro:
            return ""
        return cls.encode_offset(fro - to + cls.STOP_OFFSET)

    @classmethod
    def enc_bra_offsets(cls, tos, fro):
        """Encode the distances from FRO to each TO, as above, in the
           minimum number of bytes for a BRANCH state.  Returns a vector
           of encoded offsets, padded to the width of the widest.  The
           strings are all backward, but the vector is *not*.

           Some TOs may be strings instead of numbers.  In that case
           they are assumed to be stop codes, not deltas, and are padded
           to the necessary width but are otherwise unchanged."""
        encoded = [(cls.encode_offset(fro - to + cls.STOP_OFFSET)
                    if isinstance(to, numbers.Number)
                    else to)
                   for to in tos]
        reqlen = max(len(te) for te in encoded)
        return [te + chr(0)*(reqlen - len(te)) for te in encoded]

    @classmethod
    def emit_opcodes_c(cls, outf):
        opcodes = []
        maxnlen = 0
        for name in dir(cls):
            if name[0] not in string.ascii_uppercase: continue
            maxnlen = max(maxnlen, len(name))
            if name.startswith("STOP_"): seq = 0
            elif name.startswith("TAG_"): seq = 1
            elif name.startswith("OP_"): seq = 2
            elif name.startswith("WIDTH_"): seq = 3
            else: seq = 4
            opcodes.append((seq, getattr(cls, name), name))
        opcodes.sort()

        outf.write("\n/* Opcode definitions. */\n\n")
        x0 = 0
        for x, val, name in opcodes:
            if x0 != x:
                outf.write("\n")
                x0 = x
            outf.write("#define {0:<{1}} 0x{2:02X}\n"
                       .format(name, maxnlen, val))

        outf.write(
            "\n/* Helpers. */\n\n"
            "#define GET_TAG(op)    (((op) & TAG_MASK) >> TAG_SHIFT)\n"
            "#define GET_OP(op)      ((op) & OP_MASK)\n"
            "#define GET_WIDTH(op)  (((op) & WIDTH_MASK) >> WIDTH_SHIFT)\n"
            "#define GET_LENGTH(op, len) \\\n"
            "  (((op) & LENGTH_MASK) == LENGTH_EXTENDED ? (len) : \\\n"
            "   ((op) & LENGTH_MASK) + ((GET_OP(op) == OP_BRA) \\\n"
            "                           ? LENGTH_OFFSET_BRA \\\n"
            "                           : LENGTH_OFFSET_LIT))\n"
            "#define GET_TEXT_OFFSET(op) \\\n"
            "  (((op) & LENGTH_MASK) == LENGTH_EXTENDED ? 2 : 1)\n")

    @classmethod
    def stop_symbol(cls, code):
        if isinstance(code, str):
            code = ord(code)
        if code == Opcode.STOP_THIS:   return "!"
        if code == Opcode.STOP_NORMAL: return "+"
        if code == Opcode.STOP_ALL:    return "*"
        raise RuntimeError("{!r} is not a stop code".format(code))

    @classmethod
    def is_stop_code(cls, code):
        if isinstance(code, str):
            if len(code) > 1: return False
            code = ord(code)
        return Opcode.STOP_NORMAL <= code <= Opcode.STOP_THIS

class State(object):
    """One state of the DFA under construction. States are hashable
       and comparable for equality; two states are equal if and only
       if they have the same "right language" in the paper's
       terminology (i.e. all of their descendants are equal,
       recursively).

       State objects start out as just a set of out-edges, which is a
       dictionary indexed by character.  A state is final if and only
       if it has no out-edges.  In that case it will be reached by an
       epsilon transition, denoted by the out-edge being one of the
       three special values STOP_THIS, STOP_NORMAL, or STOP_ALL.

       After the DFA is fully constructed, all epsilon transitions are
       removed; instead, some states reachable by a normal transition
       will have a 'stop_code' field which is one of the above special
       values.  These states are maybe-final; they may have out-edges,
       in which case they are a *candidate* match, but a longer match
       is still possible.  Or they may have no out-edges, in which
       case they are the longest possible match.

       After removal of epsilon transitions, chains of states with
       only one in- and out-edge are merged.
       """

    def __init__(self):
        self.o = {}

        # Ancillary data.
        self.in_edges = []
        self.offset = None
        self.last_child = None
        self.stop_code = None
        self.dump_mark = 0

    def __eq__(self, other):
        if len(self.o) != len(other.o):
            return False
        ks = set(self.o.keys())
        for k in other.o.keys():
            if k not in ks:
                return False
            if self.o[k] != other.o[k]:
                return False
            ks.remove(k)
        return not ks

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return (hash(",".join(self.o.keys())) ^
                reduce(lambda a, v: a ^ hash(v), self.o.values(), 0))

    # Methods used during DFA construction.  These assume that the
    # state-merging optimization (below) has not occurred.

    def add_suffix(self, suffix):
        """Construct a chain of states which recognize the string
           SUFFIX, starting from the current state.  Logically a
           recursive algorithm, but has been converted to
           iteration."""

        cur = self
        for ch in suffix:
            # We should not be trying to add a character which is
            # already in the transition graph, because that would
            # mean that find_extension_point found the wrong point.
            assert ch not in cur.o
            cur.last_child = (ch, State())
            cur.o[ch] = cur.last_child[1]
            cur = cur.last_child[1]

    def find_extension_point(self, word):
        """Locate the longest prefix of WORD which is recognized by
           the DFA rooted at SELF.  Return the state reached by
           matching the last character of that prefix, and the
           remainder of WORD."""

        cur = self
        for i, ch in enumerate(word):
            succ = cur.o.get(ch)
            if not succ:
                return cur, word[i:]
            cur = succ

        # Duplicate word in the input set?
        if not cur.o:
            sys.stderr.write("warning: duplicated entry for '%s'\n"
                             % word[:-1])
            return None, ""

        # If we get here, WORD is a proper prefix of some word already
        # in the dictionary.  This is supposed to be impossible (because
        # WORD is constructed to end with one of the stop codes, which
        # cannot appear in the middle of a word).
        raise RuntimeError("%s completely matched including stop code?!"
                           % repr(word))

    def replace_or_register(self, register):
        """If REGISTER contains a state equivalent to the most recently
           added child of this state, replace the child with the state in
           the register."""

        if self.last_child is None: return
        val, child = self.last_child
        if child.o:
            child.replace_or_register(register)

        candidate = register.get(child, None)
        if candidate is not None:
            if candidate is not child:
                self.o[val] = candidate
                self.last_child = (val, candidate)
        else:
            register[child] = child

    # State-merging optimizations.  Must not be called until the
    # DFA is fully constructed.

    def merge_epsilon_states(self):
        """Recursively merge final states into their parents.
           Whenever we have
               self +---> (final)
                    +...
           the epsilon transition can be deleted and the stop code for
           the final state applied to 'self'."""

        for stop in (Opcode.STOP_THIS, Opcode.STOP_NORMAL, Opcode.STOP_ALL):
            epsilon = chr(stop)
            final = self.o.get(epsilon)
            if final is not None:
                assert len(final.o) == 0
                assert self.stop_code is None
                self.stop_code = stop
                del self.o[epsilon]

        for child in self.o.values():
            child.merge_epsilon_states()

    def find_in_edges(self):
        """Find all of the edges pointing into SELF and its children,
           recursing down the tree."""
        # Note: 'in_edges' is not a set because we want 'is' comparisons
        # here, not '==' comparisons.
        for child in self.o.values():
            for x in child.in_edges:
                if x is self: break
            else:
                child.in_edges.append(self)
            child.find_in_edges()

    def merge_chains(self):
        """Recursively merge chains of states that perform no branching.
           Whenever we have
               self --a--> child --b--> grand,
           where (a) SELF's only successor is CHILD,
                 (b) CHILD has no other in-edges, and
                 (c) CHILD has no other out-edges,
           then we can rewrite this portion of the graph as
               self --ab--> grand.

           Relies on find_in_edges having already been called."""

        if len(self.o) == 1:
            val, child = self.o.items()[0]
            assert len(child.in_edges) >= 1

            while (len(child.o) == 1 and len(child.in_edges) == 1 and
                   child.stop_code is None):
               cval, grand = child.o.items()[0]

               # We don't just call remove() here because that would
               # do an == comparison rather than an 'is' comparison.
               for i, pred in enumerate(grand.in_edges):
                   if pred is child:
                       break
               else:
                   raise RuntimeError(
                       "child should have been in grand's in-edges")
               grand.in_edges[i] = self

               del self.o[val]

               child = grand
               val += cval
               self.o[val] = child

        for child in self.o.values():
            child.merge_chains()

    def merge_states(self):
        self.merge_epsilon_states()
        self.find_in_edges()
        self.merge_chains()

    # Output methods.

    def dump_r(self, outf, depth, mark):
        outf.write(" ")
        depth += 1

        if self.dump_mark == mark:
            outf.write("[")
            depth += 1
        else:
            self.dump_mark = mark

        if self.stop_code is not None:
            outf.write(Opcode.stop_symbol(self.stop_code))
            depth += 1

        first = True
        for val, child in sorted(self.o.items()):
            assert len(val) >= 1
            if Opcode.is_stop_code(val):
                val = Opcode.stop_symbol(val)
            if first:
                first = False
            else:
                outf.write("\n" + " "*depth)
            outf.write(val)
            child.dump_r(outf, depth + len(val), mark)

    def dump(self, outf, depth=0):
        mark = self.dump_mark + 1
        self.dump_r(outf, depth, mark)

    def serialize_1(self, buf, children):
        """Generate the string representation of SELF, not including
           children (but including the offset-to-children table), into
           OBUF.  Note that the sequence of bytes emitted is in reverse
           order; this is so we can reverse the entire string blindly
           when we're done, producing a preorder DFA from the postorder
           traversal below."""

        if len(children) == 0:
            # Terminal state. Don't do anything now; serialize_1 on our
            # parent will pack us into the offset table.
            assert self.stop_code is not None
            return

        end_offset = buf.tell()

        if len(children) == 1:
            # LITERAL state.
            # The state format is
            #    LITERAL/wl [l] text o
            # The next 'l' characters are compared with 'text'.
            # If they match, advance to state 'o', otherwise fail.
            # LITERAL->STOP is encoded with LITERAL1 and the stop code
            # in the 'o' field, rather than LITERAL0 and the stop code
            # as its own state.
            val, child = children[0]
            if len(child.o) == 0:
                assert Opcode.is_stop_code(child.stop_code)
                if len(val) == 1 and self.stop_code is None:
                    buf.write(Opcode.encode_special(child.stop_code))
                    buf.write(Opcode.encode_special(val))
                else:
                    buf.write(chr(child.stop_code))
                    buf.write("".join(reversed(val)))
                    buf.write(Opcode.encode_normal(self.stop_code,
                                                   Opcode.OP_LIT,
                                                   1, len(val)))
            else:
                # How big an offset do we need?
                enc = Opcode.enc_lit_offset(child.offset, end_offset)
                if len(enc) == 0 and len(val) == 1 and self.stop_code is None:
                    buf.write(Opcode.encode_special(val))
                else:
                    buf.write(enc)
                    buf.write("".join(reversed(val)))
                    buf.write(Opcode.encode_normal(self.stop_code,
                                                   Opcode.OP_LIT,
                                                   len(enc), len(val)))
        else:
            # BRANCH state.  Note that 'children' is already sorted.
            # The state format is
            #    BRANCH/wl [l] a b c ... oa ob oc ...
            # The next character is compared with 'a', 'b', 'c', etc.
            # If it is equal to one of these characters, advance to
            # the state indicated by the corresponding 'o' field,
            # otherwise fail the match.
            targets = []
            vals = []
            for v, c in children:
                assert len(v) == 1
                vals.append(v)
                if len(c.o) == 0:
                    assert Opcode.is_stop_code(c.stop_code)
                    targets.append(chr(c.stop_code))
                else:
                    targets.append(c.offset)
            deltas = Opcode.enc_bra_offsets(targets, end_offset)
            if len(deltas[0]) == 1 and len(set(deltas)) == 1:
                dlen = 0
                buf.write(deltas[0])
            else:
                dlen = len(deltas[0])
                buf.write("".join(reversed(deltas)))

            buf.write("".join(reversed(vals)))
            buf.write(Opcode.encode_normal(self.stop_code, Opcode.OP_BRA,
                                           dlen, len(vals)))

        self.offset = buf.tell()

    def serialize_r(self, buf):
        """Generate the string representation of SELF (and all its children)
           into OBUF.  This is done in post-order so that we know the offset
           of every child when it comes time to serialize ourselves. """

        if self.offset is not None:
            # This state (and all its descendants) have already been
            # serialized.  Do not do it again.
            return

        children = sorted(self.o.items())
        for val, child in children:
            child.serialize_r(buf)
        self.serialize_1(buf, children)

    def serialize(self):
        """Generate and return the packed string representation of the DFA."""
        buf = cStringIO.StringIO()
        self.serialize_r(buf)
        return "".join(reversed(buf.getvalue()))

#
# High-level output.
#

_to_c_identifier_tr = \
    string.maketrans(string.punctuation, "_"*len(string.punctuation))
def to_c_identifier(s):
    return s.upper().translate(_to_c_identifier_tr)

def emit_dfa_c_verbose(dfabytes, outf):
    """Generate a C data object from the DFA in 'dfabytes'.
       In verbose mode, we decode it a little and print out each field
       differently, in order to make the generated DFA easier to debug."""

    state = 0
    for idx, byte in enumerate(dfabytes):
        nbyte = ord(byte)
        if state == 0: # beginning of a state
            outf.write("\n/* {:04X} */ 0x{:02X},".format(idx, nbyte))

            if (nbyte & Opcode.TAG_MASK) >> Opcode.TAG_SHIFT \
                    == Opcode.TAG_SPECIAL:
                val = nbyte & ~Opcode.TAG_MASK
                if val <= Opcode.STOP_OFFSET:
                    outf.write("  /* 0x{:02X} | 0x{:02X} */"
                               .format(Opcode.TAG_MASK, val))
                else:
                    outf.write("  /* 0x{:02X} | '{:s}'-32 */"
                               .format(Opcode.TAG_MASK, chr(val+32)))
                continue

            nlen  = 0
            count = 0
            lit = (nbyte & Opcode.OP_MASK) != Opcode.OP_BRA
            width = (nbyte & Opcode.WIDTH_MASK) >> 3

            if (nbyte & Opcode.LENGTH_MASK) != Opcode.LENGTH_EXTENDED:
                state = 2
                nlen = (nbyte & Opcode.LENGTH_MASK)
                if lit:
                    nlen += Opcode.LENGTH_OFFSET_LIT
                else:
                    nlen += Opcode.LENGTH_OFFSET_BRA
            else:
                state = 1

        elif state == 1: # extended length byte
            outf.write(" {: 3d},".format(nbyte))
            nlen = nbyte
            state = 2

        elif state == 2: # text
            if count == 0: outf.write(" ")
            outf.write(" '{}',".format(byte))
            count += 1
            if count == nlen:
                if width == 0:
                    if lit:
                        state = 0
                    else:
                        width = 1
                        nlen = 1
                        count = 0
                        state = 3
                else:
                    if lit: nlen  = width
                    else:   nlen *= width
                    count = 0
                    state = 3

        elif state == 3: # offsets
            if count % width == 0: outf.write(" ")
            outf.write(" 0x{:02X},".format(nbyte))
            count += 1
            if count == nlen:
                state = 0

def emit_dfa_c(dfabytes, outf):
    """Same as above, but just dumps the table as a giant blob of numbers."""
    coded = ", ".join("{:d}".format(ord(c)) for c in dfabytes)
    outf.write(textwrap.fill(coded, width=78, initial_indent="  ",
                             subsequent_indent="  ", break_long_words=False))

def emit_mod_c(dfa, input_fname, output_fname, license_text):
    """Write out a complete C header file that defines DFA plus the
       opcode constants used in its encoding."""

    with open(output_fname + ".tmp", "w") as outf:
        outf.write("/* Generated by {} from {}. DO NOT EDIT.\n"
                   " * Mechanically derived from material under the "
                       "following license terms:\n"
                   " *"
                   "{}\n"
                   " */\n\n"
                   .format(os.path.basename(sys.argv[0]), input_fname,
                           "".join("\n * "+l for l in license_text)))

        outf.write("#ifndef {0}__\n#define {0}__\n"
                   .format(to_c_identifier(os.path.basename(output_fname))))

        outf.write(
            "\n#if '-' != 45 || '.' != 46 || '0' != 48 || '9' != 57 || \\\n"
            "    'A' != 65 || 'Z' != 90\n"
            "#error \"DFA encoding assumes ASCII.\"\n"
            "#endif\n")

        Opcode.emit_opcodes_c(outf)

        if VERBOSE:
            outf.write("\n/* Decision tree is:\n\n     ")
            dfa.dump(outf, depth=5)
            outf.write("\n*/\n")

        outf.write("\nstatic const unsigned char tld_dfa[] = {\n")
        if VERBOSE:
            emit_dfa_c_verbose(dfa.serialize(), outf)
        else:
            emit_dfa_c(dfa.serialize(), outf)
        outf.write("\n};\n")

        outf.write("\n#endif /* {} */\n".format(os.path.basename(output_fname)))

    try:
        os.remove(output_fname) # yay Windows
    except EnvironmentError, e:
        if e.errno != errno.ENOENT:
            raise

    os.rename(output_fname + ".tmp", output_fname)

#
# Input.
#

def build_dfa(domains):
    """Construct a DFA which recognizes all of the domain (suffixes)
       in DOMAINS.  This is the part which is roughly Algorithm 1 from
       the paper "Incremental Construction of Minimal Acyclic
       Finite-State Automata" mentioned at the top of the file."""
    root = State()
    register = {}
    for domain in domains:
        (last_state, suffix) = root.find_extension_point(domain)
        if last_state is None:
            continue
        if last_state.o:
            last_state.replace_or_register(register)
        last_state.add_suffix(suffix)
    root.replace_or_register(register)
    return root

def check_std3(fname, lnum, domain):
    # STD 3 specifies that no label in a domain may contain byte
    # values 00..2C, 2E..2F, 3A..40, 5B..60, or 7B..7F. After IDNA
    # encoding and lowercasing, 41..5A and 80..FF should also not
    # appear.  Also, no label may begin or end with byte 2D (U+002D
    # HYPHEN-MINUS).

    ok_chars = frozenset("-0123456789abcdefghijklmnopqrstuvwxyz")

    for label in domain.split("."):
        if len(label) == 0:
            sys.stderr.write("{}:{}: warning: '{}' contains an empty label\n"
                             .format(fname, lnum+1, domain))
            continue

        if label[0] == "-":
            sys.stderr.write(
                "{}:{}: warning: '{}' contains a label beginning with '-'\n"
                .format(fname, lnum+1, domain))
        if len(label) > 1 and label[-1] == "-":
            sys.stderr.write(
                "{}:{}: warning: '{}' contains a label ending with '-'\n"
                .format(fname, lnum+1, domain))

        for c in label:
            if c not in ok_chars:
                sys.stderr.write(
                    "{}:{}: warning: '{}' contains invalid character '{}'\n"
                    .format(fname, lnum+1, domain, c))

def read_tld_names(fname):
    license_text = []
    domains = []
    state = 0
    error = False
    with open(fname, "rU") as f:
        for lnum, line in enumerate(f):
            line = line.strip()

            # The license text is the block of comments at the very
            # top of the file, up to the first blank line.
            # Discard all other comments and blank lines.
            if line[:2] == "//":
                if state == 0:
                    license_text.append(line[2:].lstrip())
                continue
            if line == "":
                if state == 0:
                    state = 1
                continue

            # According to http://publicsuffix.org/list/, rule lines are
            # "only read up to the first whitespace".  The current file
            # doesn't have anything after whitespace on a rule line, so
            # warn if we see something.
            ls = line.split(None, 1)
            line = ls[0]
            if len(ls) > 1:
                sys.stderr.write("{}:{}: warning: junk after rule: {!r}\n"
                                 .format(fname, lnum+1, ls[1]))

            # Check for the two special types of rules.
            if line[0] == "!":
                if len(line) < 2:
                    sys.stderr.write("{}:{}: invalid use of '!'"
                                     .format(fname, lnum+1))
                    error = True
                    continue

                rtype = Opcode.STOP_THIS
                line = line[1:]

            elif line[0] == "*":
                if len(line) < 3 or line[1] != ".":
                    sys.stderr.write("{}:{}: invalid use of '*'"
                                     .format(fname, lnum+1))
                    error = True
                    continue

                rtype = Opcode.STOP_ALL
                line = line[2:]
            else:
                rtype = Opcode.STOP_NORMAL

            assert len(line) > 0
            if line[0] == ".":
                sys.stderr.write("{}:{}: rule should not start with a dot"
                                 .format(fname, lnum+1))
                error = True
                continue

            # Technically asterisks are allowed to appear in the middle
            # of a rule, but currently none do.
            if "*" in line:
                sys.stderr.write(
                    "{}:{}: cannot handle '*' in the middle of a rule\n"
                    .format(fname, lnum+1))
                error = True
                continue

            # Convert to Punycode and force lowercase, then check STD3
            # compliance.
            line = line.decode("utf-8").encode("idna").lower()
            check_std3(fname, lnum, line)

            # Input to the DFA-generation algorithm is the *reversal* of the
            # line, with the rule code appended, back in uppercase (the
            # "hypercompact literal" optimization requires uppercase; the
            # matcher will take care of case insensitivity).
            domains.append("".join(reversed(line.upper())) + chr(rtype))

    if error:
        raise SystemExit(1)

    domains.sort()
    return domains, license_text

def main(argv):
    if argv[1] == "-v" or argv[1] == "--verbose":
        global VERBOSE
        VERBOSE = True
        argv.pop(0)

    domains, license_text = read_tld_names(argv[1])

    dfa = build_dfa(domains)
    dfa.merge_states()
    emit_mod_c(dfa, argv[1], argv[2], license_text)

if __name__ == '__main__': main(sys.argv)
