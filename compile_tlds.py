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

#
# DFA compression and serialization.
#

class Opcode(object):
    """Opcodes used in the serialized representation of the DFA.
       Every state has an opcode, which defines both the operation to
       perform next, and the sizes of certain fields within the state."""

    # Stop codes, corresponding to the three types of rule.
    #
    # Stop codes are packed into the out-edge table of the parent state
    # rather than being assigned states of their own.  Stop codes are
    # also recycled to tag words in the input dictionary so that the
    # DFA construction algorithm does not unify paths where
    # inappropriate.  Therefore, they must not collide with the valid
    # set of characters in input words.  Further, to facilitate
    # packing them into the out-edge table, they should all be
    # consecutive and at one end of the number space; we use the
    # bottom end.
    #
    # The three types of rule receive a rather confusing definition in
    # the spec, but it amounts to the following: if a rule with type X
    # is the longest match for a domain name, then the registered
    # domain is:
    STOP_FAIL    = 0x00  # error
    STOP_THIS    = 0x01  # the current match
    STOP_NORMAL  = 0x02  # the current match plus one label
    STOP_ALL     = 0x03  # the current match plus two labels

    STOP_OFFSET = 0x04 # subtract this from out-edges >= this to get an offset

    # Stop codes can also appear as the high bits of a regular state's
    # opcode.  This happens when one rule is a proper prefix of
    # another rule.  All such opcodes have the highest bit set, to
    # avoid collisions with the ASCII printable space (this might not
    # be necessary, but it appeals to my sense of tidiness).
    MAYBE_STOP_MASK   = 0xE0
    MAYBE_STOP_THIS   = 0x80
    MAYBE_STOP_NORMAL = 0xA0
    MAYBE_STOP_ALL    = 0xC0

    # N-way branch.
    # The state format is
    #    BRANCHx | n | a b c ... | oa ob oc ... |
    # The next character is compared with 'a', 'b', 'c' (there are 'n'
    # possibilities.  If it is equal to one of these characters, advance
    # to the state indicated by the corresponding 'o' field, otherwise
    # fail the match.
    # 'o' fields are either stop codes, or the positive offset from
    # the end of this state to the next state, plus STOP_OFFSET.  'x'
    # determines how wide the out edges are: 1, 2, 3, or 4 bytes each.
    # When out-edges are more than 1 byte wide, they are big-endian.

    OP_BRANCH1 = 0x04
    OP_BRANCH2 = 0x05
    OP_BRANCH3 = 0x06
    OP_BRANCH4 = 0x07

    # Literal string match.
    # The state format is
    #    LITERALx | n | text | o |
    # The next 'n' characters are compared with 'text'.  If they
    # match, advance to state 'o', otherwise fail.
    # 'o' is encoded as for BRANCHx; as an additional space
    # optimization there is a LITERAL0 which omits the 'o' field
    # entirely -- the displacement to the next opcode is zero (from
    # the end of 'text').  LITERAL->STOP is encoded with LITERAL1 and
    # the stop code in the 'o' field, rather than LITERAL0 and the
    # stop code as its own state.
    OP_LITERAL0 = 0x08
    OP_LITERAL1 = 0x09
    OP_LITERAL2 = 0x0A
    OP_LITERAL3 = 0x0B
    OP_LITERAL4 = 0x0C

    @classmethod
    def encode(cls, main, stop):
        """Combine a main opcode and a stop code."""
        if not ( cls.OP_BRANCH1 <= main <= cls.OP_LITERAL4 ):
            raise RuntimeError("bad main: {!r}".format(main))
        assert stop is None or cls.STOP_THIS <= stop <= cls.STOP_ALL
        if stop is None:            return chr(main)
        elif stop == cls.STOP_THIS:   return chr(main | cls.MAYBE_STOP_THIS)
        elif stop == cls.STOP_NORMAL: return chr(main | cls.MAYBE_STOP_NORMAL)
        elif stop == cls.STOP_ALL:    return chr(main | cls.MAYBE_STOP_ALL)
        else:
            raise RuntimeError("can't get here")

    @staticmethod
    def encode_offset(delta):
        """Encode the distance DELTA in the minimum possible number
           of bytes, and return it.  Note that the string is emitted
           backward, because the entire DFA will be reversed when
           we're done generating it."""
        if delta < 256:
            return chr(delta)
        elif delta < 256*256:
            return (chr((delta & 0x00FF)     ) +
                    chr((delta & 0xFF00) >> 8))
        elif delta < 256*256*256:
            return (chr((delta & 0x0000FF)      ) +
                    chr((delta & 0x00FF00) >>  8) +
                    chr((delta & 0xFF0000) >> 16))
        else:
            assert delta < 256*256*256*256
            return (chr((delta & 0x000000FF)      ) +
                    chr((delta & 0x0000FF00) >>  8) +
                    chr((delta & 0x00FF0000) >> 16) +
                    chr((delta & 0xFF000000) >> 24))

    @classmethod
    def enc_lit_offset(cls, to, fro):
        """Encode the absolute distance from FRO to TO (both of which
           are byte counts, with FRO >= TO) in the minimum number of
           bytes for a LITERAL node. Return an appropriately encoded
           string and opcode."""
        if to == fro:
            return (cls.OP_LITERAL0, "")
        encoded = cls.encode_offset(fro - to + cls.STOP_OFFSET)
        return (cls.OP_LITERAL0 + len(encoded), encoded)

    @classmethod
    def enc_bra_offsets(cls, tos, fro):
        """Encode the distances from FRO to each TO, as above, in the
           minimum number of bytes for a BRANCH node.  Returns a vector
           of encoded offsets, padded to the width of the widest.

           Some TOs may be strings instead of numbers.  In that case
           they are assumed to be stop codes, not deltas, and are left
           intact.
           """
        encoded = [(cls.encode_offset(fro - to + cls.STOP_OFFSET)
                    if isinstance(to, numbers.Number)
                    else to)
                   for to in tos]
        reqlen = max(len(te) for te in encoded)
        return (cls.OP_BRANCH1 + reqlen - 1,
                [te + chr(0)*(reqlen - len(te)) for te in encoded])

    @classmethod
    def emit_opcodes_c(cls, outf):
        opcodes = []
        maxnlen = 0
        for name in dir(cls):
            if name[0] not in string.ascii_uppercase: continue
            maxnlen = max(maxnlen, len(name))
            if name.startswith("STOP_"): seq = 0
            elif name.startswith("MAYBE_"): seq = 1
            else: seq = 2
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

    @classmethod
    def stop_symbol(cls, code):
        if isinstance(code, str):
            code = ord(code)
        if code == Opcode.STOP_FAIL:   return "@"
        if code == Opcode.STOP_THIS:   return "!"
        if code == Opcode.STOP_NORMAL: return "+"
        if code == Opcode.STOP_ALL:    return "*"
        raise RuntimeError("{!r} is not a stop code".format(code))

    @classmethod
    def is_stop_code(cls, code):
        if isinstance(code, str):
            if len(code) > 1: return False
            code = ord(code)
        return Opcode.STOP_FAIL <= code <= Opcode.STOP_ALL

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
       removed; instead, some nodes reachable by a normal transition
       will have a 'stop_code' field which is one of the above special
       values.  These nodes are maybe-final; they may have out-edges,
       in which case they are a *candidate* match, but a longer match
       is still possible.  Or they may have no out-edges, in which
       case they are the longest possible match.

       After removal of epsilon transitions, chains of nodes with
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
        """If REGISTER contains a node equivalent to the most recently
           added child of this node, replace the child with the node in
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

    def merge_epsilon_nodes(self):
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
            child.merge_epsilon_nodes()

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
        """Recursively merge chains of nodes that perform no branching.
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
        self.merge_epsilon_nodes()
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
            # Terminal node. Don't do anything now; serialize_1 on our
            # parent will pack us into the offset table.
            assert self.stop_code is not None
            return

        end_offset = buf.tell()

        if len(children) == 1:
            # LITERAL node.
            val, child = children[0]
            assert 0 < len(val) <= 255
            if len(child.o) == 0:
                assert child.stop_code is not None
                assert Opcode.STOP_THIS <= child.stop_code <= Opcode.STOP_ALL
                buf.write(chr(child.stop_code))
                buf.write("".join(reversed(val)))
                buf.write(chr(len(val)))
                buf.write(Opcode.encode(Opcode.OP_LITERAL1, self.stop_code))
            else:
                # How big an offset do we need?
                (op, enc) = Opcode.enc_lit_offset(child.offset, end_offset)
                buf.write(enc)
                buf.write("".join(reversed(val)))
                buf.write(chr(len(val)))
                buf.write(Opcode.encode(op, self.stop_code))
        else:
            # BRANCH node.  Note that 'children' is known to be sorted.
            assert 2 <= len(children) <= 255
            targets = []
            vals = []
            for v, c in children:
                assert len(v) == 1
                vals.append(v)
                if len(c.o) == 0:
                    assert c.stop_code is not None
                    assert Opcode.STOP_THIS <= c.stop_code <= Opcode.STOP_ALL
                    targets.append(chr(c.stop_code))
                else:
                    targets.append(c.offset)
            (op, deltas) = Opcode.enc_bra_offsets(targets, end_offset)
            vstr = "".join(reversed(vals))
            dstr = "".join(reversed(deltas))
            buf.write(dstr)
            buf.write(vstr)
            buf.write(chr(len(children)))
            buf.write(Opcode.encode(op, self.stop_code))

        self.offset = buf.tell()

    def serialize_r(self, buf):
        """Generate the string representation of SELF (and all its children)
           into OBUF.  This is done in post-order so that we know the offset
           of every child when it comes time to serialize ourselves. """

        if self.offset is not None:
            # This node (and all its descendants) have already been
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

def emit_dfa_c(dfabytes, outf):
    """Generate a C data object from the DFA in 'dfabytes'.
       We could just dump it out as a string, but instead we
       decode it a little and print out each field differently,
       in order to make the generated DFA easier to debug."""

    outf.write("\nstatic const unsigned char tld_dfa[] = {")

    state = 0
    width = 0
    lit   = False
    nlen  = 0
    count = 0
    for idx, byte in enumerate(dfabytes):
        nbyte = ord(byte)
        if state == 0: # beginning of a node
            outf.write("\n/* {:04X} */ 0x{:02X},".format(idx, nbyte))
            op = (nbyte & ~Opcode.MAYBE_STOP_MASK)
            assert Opcode.OP_BRANCH1 <= op <= Opcode.OP_LITERAL4
            if op <= Opcode.OP_BRANCH4:
                lit   = False
                width = 1 + op - Opcode.OP_BRANCH1
            else:
                lit   = True
                width = op - Opcode.OP_LITERAL0
            state = 1

        elif state == 1: # length byte
            outf.write(" {: 3d},".format(nbyte))
            nlen = nbyte
            state = 2
            count = 0

        elif state == 2: # text
            if count == 0: outf.write(" ")
            outf.write(" '{}',".format(byte))
            count += 1
            if count == nlen:
                if width == 0:
                    state = 0
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

    outf.write("\n};\n")

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

        Opcode.emit_opcodes_c(outf)

        #outf.write("\n/* Decision tree is:\n\n     ")
        #dfa.dump(outf, depth=5)
        #outf.write("\n*/\n")

        outf.write("\n/* DFA. */\n")

        emit_dfa_c(dfa.serialize(), outf)

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

            # Convert to Punycode and force lowercase.
            # (The IDNA encoder does not apply nameprep to all-ASCII labels.
            # It is my understanding that the only effect nameprep can have
            # on an all-ASCII label is to force it to lowercase.)
            line = line.decode("utf-8").encode("idna").lower()
            check_std3(fname, lnum, line)

            # Input to the DFA-generation algorithm is the *reversal* of the
            # line, with the rule code appended.
            domains.append("".join(reversed(line)) + chr(rtype))

    if error:
        raise SystemExit(1)

    domains.sort()
    return domains, license_text

def main(argv):
    domains, license_text = read_tld_names(argv[1])

    dfa = build_dfa(domains)
    dfa.merge_states()
    emit_mod_c(dfa, argv[1], argv[2], license_text)

if __name__ == '__main__': main(sys.argv)
