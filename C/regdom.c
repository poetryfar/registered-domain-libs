/*
 * Calculate the effective registered domain of a fully qualified domain name.
 *
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to you under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at:
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * Florian Sager, 03.01.2009, sager@agitos.de, http://www.agitos.de
 * Ward van Wanrooij, 04.04.2010, ward@ward.nu
 * Ed Walker, 03.10.2012
 *
 */

#include <stdlib.h>
#include <string.h>
#include "regdom.h"

#define MATCH_FAIL ((unsigned int)-1)

/* static data */

#include "tld-canon.h"

/* The encoded DFA uses exclusively capital letters; our input may be
   any case.  (IDNA encoding, however, is caller's responsibility.) */
static inline unsigned char
casefold(char cs)
{
    unsigned char c = cs;
    if ('a' <= c && c <= 'z')
        c = c - 'a' + 'A';
    return c;
}

static unsigned int
decode_offset(const unsigned char *optr, unsigned int len, unsigned int nodelen)
{
    unsigned int offset = 0;
    if (len == 0)
        return offset + nodelen + STOP_OFFSET;

    do
    {
        // Regardless of how many bits actually fit in an 'unsigned char',
        // the DFA generator puts 8 bits of the number in each.
        // (The C standard guarantees at least 8 bits will fit.)
        offset = offset*256 + *optr;
        optr++;
    }
    while (--len);

    if (offset < STOP_OFFSET)
        return offset;
    return offset + nodelen;
}

static unsigned int
process_branch(char cs,
               const unsigned char *restrict dfanode,
               unsigned int op)
{
    unsigned int dwidth = GET_WIDTH(op);
    unsigned int len    = GET_LENGTH(op, dfanode[1]);
    const unsigned char *text = dfanode + GET_TEXT_OFFSET(op);

    // Binary search in [text, text+len) for c.
    unsigned char c = casefold(cs);
    const unsigned char *lo = text;
    const unsigned char *hi = lo + len - 1;
    const unsigned char *md;
    while (hi >= lo)
    {
        md = lo + (hi-lo)/2;
        unsigned char d = *md;
        if (d < c)
            lo = md + 1;
        else if (d > c)
            hi = md - 1;
        else
            goto match;
    }
    return MATCH_FAIL;

 match:;
    unsigned int delta = GET_TEXT_OFFSET(op) + len;
    if (dwidth == 0)
        return decode_offset(dfanode + delta, 1, delta + 1);
    else
    {
        unsigned int idx    = md - text;
        return decode_offset(dfanode + delta + idx*dwidth,
                             dwidth,   delta + len*dwidth);
    }
}

static unsigned int
process_literal(const char *cur,
                const char *head,
                const unsigned char *restrict dfanode,
                unsigned int op)
{
    unsigned int dwidth = GET_WIDTH(op);
    unsigned int len    = GET_LENGTH(op, dfanode[1]);
    unsigned int delta  = GET_TEXT_OFFSET(op);
    if (len == 0) abort();

    do
    {
        if (cur == head)
            return MATCH_FAIL;
        if (casefold(cur[-1]) != dfanode[delta])
            return MATCH_FAIL;

        delta++;
        cur--;
    }
    while (--len);

    // if we get here, we have successfully matched the entire op
    return decode_offset(dfanode+delta, dwidth, delta+dwidth);
}

// Possibly record the current position, CUR, as the current longest match,
// with type OP. (in *MATCH and *MATCH_TYPE)  HEAD is the beginning of the
// string.
static void
candidate_match(unsigned int op,
                const char *cur,
                const char *head,
                const char **restrict match,
                unsigned int *restrict match_type)
{
    if (op == MATCH_FAIL)
        return;

    // Regardless of opcode, this cannot be a match if it is in
    // the middle of a label.  (No need to casefold here.)
    if (cur != head && cur[-1] != '.')
        return;

    *match = cur;

    if (op & TAG_MASK)
        switch (GET_TAG(op))
        {
        case TAG_NORMAL_S: *match_type = STOP_NORMAL; break;
        case TAG_ALL_S:    *match_type = STOP_ALL;    break;
        default: abort();
        }
    else
        switch (op)
        {
        case STOP_THIS:
        case STOP_NORMAL:
        case STOP_ALL:
            *match_type = op;
            break;

        default:
            abort();
        }
}

// MATCH is the longest match, and OP is its type.  Confirm that we
// have enough labels in total for a match of this type to succeed,
// then return the registered domain.
static char *
check_match(const char *head, const char *match, unsigned int op)
{
    if (match == 0)
        return 0;

    switch (op)
    {
    default:
        abort();

    case MATCH_FAIL:
        return 0; // no match

    case STOP_ALL:
        // Two additional labels are required.
        if (match == head)
            return 0;
        if (match[-1] == '.')
            match -= 2;
        else if (match[0] != '\0')
            abort();

        while (match > head && match[-1] != '.')
            match--;

        // fall through

    case STOP_NORMAL:
        // One additional label is required.
        if (match == head)
            return 0;
        if (match[-1] == '.')
            match -= 2;
        else if (match[0] != '\0')
            abort();

        while (match > head && match[-1] != '.')
            match--;

        // fall through

    case STOP_THIS:
        // No additional labels are required.
        break;
    }

    // Converting const char * to char * here is necessary so that the
    // public API may be applied to both const char * and char * strings
    // (same logic as applies to many string.h functions).
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wcast-qual"
    return (char *)match;
#pragma GCC diagnostic pop
}

char *
getRegisteredDomainDrop(const char *hostname, int drop_unknown)
{
    // Eliminate some special (always-fail) cases first.
    if (hostname[0] == '.' || hostname[0] == '\0')
        return 0;

    // The registered domain will always be a suffix of the input hostname.
    // Start at the end of the name and work backward.
    const char *head  = hostname;
    const char *cur   = hostname + strlen(hostname);

    // If no published rule matches, the official default is "*", i.e.
    // take the last two labels.  Caller can request that we return
    // NULL instead.
    const char *match;
    unsigned int match_type;
    if (drop_unknown)
    {
        match = 0;
        match_type = MATCH_FAIL;
    }
    else
    {
        match = cur;
        match_type = STOP_ALL;
    }

    const unsigned char *restrict dfanode = tld_dfa;
    unsigned int delta, op;

    for (;;)
    {
        op = *dfanode;
        if (GET_TAG(op) == TAG_SPECIAL)
        {
            op &= ~TAG_MASK;
            if (op == STOP_NORMAL || op == STOP_ALL || op == STOP_THIS)
            {
                candidate_match(op, cur, head, &match, &match_type);
                break;
            }
            else if (cur == head || casefold(cur[-1]) != op + 32)
                break;

            dfanode += 1;
            cur -= 1;
            continue;
        }
        else if (GET_TAG(op) != 0)
            candidate_match(op, cur, head, &match, &match_type);

        if (GET_OP(op) == OP_BRA)
        {
            if (cur == head)
                break;
            delta = process_branch(cur[-1], dfanode, op);
            cur -= 1;
        }
        else
        {
            // process_literal handles being called with cur == head
            delta = process_literal(cur, head, dfanode, op);
            cur -= GET_LENGTH(op, dfanode[1]);
        }

        if (delta == MATCH_FAIL)
            break;

        if (delta < STOP_OFFSET)
        {
            candidate_match(delta, cur, head, &match, &match_type);
            break;
        }
        dfanode += delta - STOP_OFFSET;
    }

    return check_match(head, match, match_type);
}

char *
getRegisteredDomain(const char *hostname)
{
    return getRegisteredDomainDrop(hostname, 0);
}
