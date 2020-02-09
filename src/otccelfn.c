/*
  Obfuscated Tiny C Compiler with ELF output

  Copyright (C) 2001-2003 Fabrice Bellard

  This software is provided 'as-is', without any express or implied
  warranty.  In no event will the authors be held liable for any damages
  arising from the use of this software.

  Permission is granted to anyone to use this software for any purpose,
  including commercial applications, and to alter it and redistribute it
  freely, subject to the following restrictions:

  1. The origin of this software must not be misrepresented; you must not
     claim that you wrote the original software. If you use this software
     in a product, an acknowledgment in the product and its documentation
     *is* required.
  2. Altered source versions must be plainly marked as such, and must not be
     misrepresented as being the original software.
  3. This notice may not be removed or altered from any source distribution.
*/
#ifndef TINY
#include <stdarg.h>
#endif
#include <stdio.h>

/* vars: value of variables
   loc : local variable index
   glo : global variable ptr
   data: base of data segment
   ind : output code ptr
   prog: output code
   rsym: return symbol
   sym_stk: symbol stack
   dstk: symbol stack pointer
   dptr, dch: macro state

   * 'vars' format:
   For each character TAG_TOK at offset 'i' before a
    symbol in sym_stk, we have:
    v = (int *)(vars + 8 * i + TOK_IDENT)[0]
    p = (int *)(vars + 8 * i + TOK_IDENT)[0]

    v = 0    : undefined symbol, p = list of use points.
    v = 1    : define symbol, p = pointer to define text.
    v < LOCAL: offset on stack, p = 0.
    otherwise: symbol with value 'v', p = list of use points.

   * 'sym_stk' format:
   TAG_TOK sym1 TAG_TOK sym2 .... symN '\0'
   'dstk' points to the last '\0'.
*/
/* tok: Current token type.
**
** tokc: Current token's associated value.
**
** tokl: Current operator token's precedence.
**
** ch: Current character.
**
** vars: Variables' info table.
**
** rsym: Pointer to a chain of pending jump address fields for a function's
** return statements.
**
** prog: Instruction buffer.
**
** ind: Instruction buffer's current location pointer.
**
** loc: Current local variable's stack offset.
**
** glo: Data segment buffer's current location pointer.
**
** file: Input and ouput file's FILE pointer.
**
** sym_stk: Symbol stack.
**
** dstk: Symbol stack top pointer.
**
** dptr: Macro value pointer.
**
** dch: Old current character stored before reading from macro value.
**
** last_id: Last id string pointer.
**
** data: Data segment buffer.
**
** text: Text segment buffer.
**
** data_offset: Data segment offset taking ELF into account.
*/
int tok, tokc, tokl, ch, vars, rsym, prog, ind, loc, glo, file, sym_stk, dstk, dptr, dch, last_id, data, text, data_offset;

/* Buffer size. */
#define ALLOC_SIZE 99999

/* Whether generate ELF file. */
#define ELFOUT

/* depends on the init string */
#define TOK_STR_SIZE 48

/* Variables table entry's offset base for ids. */
#define TOK_IDENT    0x100

/* Variables table entry's offset for keywords.
**
** At 7JFQJ, the symbol stack is initialized as
** " int if else while break return for define main "
** The first word `int`'s space character is at index 0 (zero-based).
** 8 * 0 + 0x100 = 0x100 so `TOK_INT` is 0x100.
** The last word `main`'s space character is at index 42 (zero-based).
** 8 * 42 + 0x100 = 0x250 so `TOK_MAIN` is 0x250. */
#define TOK_INT      0x100
#define TOK_IF       0x120
#define TOK_ELSE     0x138
#define TOK_WHILE    0x160
#define TOK_BREAK    0x190
#define TOK_RETURN   0x1c0
#define TOK_FOR      0x1f8
#define TOK_DEFINE   0x218
#define TOK_MAIN     0x250

/* Token type for double tokens like `++`. */
#define TOK_DUMMY   1

/* Token type for number. */
#define TOK_NUM     2

/* Variables table entry's value threshold for local variables. */
#define LOCAL   0x200

/* Variables table entry's type for function and variable name. */
#define SYM_FORWARD 0

/* Variables table entry's type for macro name. */
#define SYM_DEFINE  1

/* Start marker for name symbol on symbol stack. */
/* tokens in string heap */
#define TAG_TOK    ' '

/* End marker for macro value on symbol stack.
** Macro value may contain space character, so it needs a different end marker.
** The end marker is pushed at 2R6C0 and checked at 759KA. */
#define TAG_MACRO  2

/* additionnal elf output defines */
#ifdef ELFOUT

#define ELF_BASE      0x08048000
#define PHDR_OFFSET   0x30

#define INTERP_OFFSET 0x90
#define INTERP_SIZE   0x13

#ifndef TINY
#define DYNAMIC_OFFSET (INTERP_OFFSET + INTERP_SIZE + 1)
#define DYNAMIC_SIZE   (11*8)

#define ELFSTART_SIZE  (DYNAMIC_OFFSET + DYNAMIC_SIZE)
#else /* ifdef TINY */
#define DYNAMIC_OFFSET 0xa4
#define DYNAMIC_SIZE   0x58

#define ELFSTART_SIZE  0xfc
#endif /* TINY */

/* size of startup code */
#define STARTUP_SIZE   17

/* size of library names at the start of the .dynstr section */
#define DYNSTR_BASE      22

#else /* ifndef ELFOUT */

#define ELF_BASE  0
#define ELFSTART_SIZE  0
#define STARTUP_SIZE   0

#endif /* ELFOUT */

/* Whether `printf_text` is enabled. */
int PRINT_ENABLED = 1;

/* Whether `printf_text_v2` is enabled.
** `printf_text_v2` is used at 3XKZ7. */
int PRINT_V2_ENABLED = 0;

/* Indentation level. */
int INDENT_LEVEL = 0;

/* Print text. */
void printf_text(char const* const fmt, ...) {
    if (!PRINT_ENABLED) {
        return;
    }

    va_list ap;
    va_start(ap, fmt);
    vfprintf(stdout, fmt, ap);
    va_end(ap);
}

/* Print text. */
void printf_text_v2(char const* const fmt, ...) {
    if (!PRINT_V2_ENABLED) {
        return;
    }

    va_list ap;
    va_start(ap, fmt);
    vfprintf(stdout, fmt, ap);
    va_end(ap);
}

/* Print indentation characters. */
void printf_indents() {
    if (!PRINT_ENABLED) {
        return;
    }

    int i;
    for (i = 0; i < INDENT_LEVEL; i++) {
        printf(":");
    }
}

/* Print start delimiter before entering function body. */
void printf_start(char const* const title) {
    if (!PRINT_ENABLED) {
        return;
    }

    printf_indents();

    printf("--- %s ---\n", title);

    INDENT_LEVEL = INDENT_LEVEL + 2;
}

/* Print end delimiter before leaving function body. */
void printf_end(char const* const title) {
    if (!PRINT_ENABLED) {
        return;
    }

    INDENT_LEVEL = INDENT_LEVEL - 2;

    printf_indents();

    printf("=== %s ===\n\n", title);
}

/* Push character to symbol stack.
** `t`: Character to push to symbol stack. */
pdef(t)
{
    /* Store character in symbol stack's top slot and increment the top
    ** pointer. */
    *(char *)dstk++ = t;
}

/* Read character. */
inp()
{
    printf_start("inp");

    /* If is reading from macro value. */
    if (dptr) {
        /* Get character from macro value. */
        ch = *(char *)dptr++;

        printf_text("ch2: 0x%02x: `%c`\n", ch, ch);

        /* 759KA
        ** If macro value end marker is met. */
        if (ch == TAG_MACRO) {
            /* Indicate reading from macro value is done. */
            dptr = 0;

            /* 7TXIG
            ** Restore the old current character stored before reading from the
            ** macro value. */
            ch = dch;

            printf_text(
                "ch3: 0x%02x, `%c`\n", (unsigned int)ch, (unsigned int)ch
            );
        }
    }
    else {
        /* Get character from input file. */
        ch = fgetc(file);

        printf_text("ch1: 0x%02x, `%c`\n", (unsigned int)ch, (unsigned int)ch);
    }
    /*    printf("ch=%c 0x%x\n", ch, ch); */

    printf_end("inp");
}

/* Test whether current character is id character. */
isid()
{
    /* Test whether current character is alphanumeric or underscore. */
    return isalnum(ch) | ch == '_';
}

/* Read escaped character if any. */
/* read a character constant */
getq()
{
    printf_start("getq");

    /* If current character is `\`, it means escaped character. */
    if (ch == '\\') {
        /* Read character. */
        inp();

        printf_text("ch4: 0x%02x, `%c`\n", (unsigned int)ch, (unsigned int)ch);

        /* If current character is `n`. */
        if (ch == 'n') {
            /* Set current character be newline. */
            ch = '\n';

            printf_text(
                "ch5: 0x%02x, `%c`\n", (unsigned int)ch, (unsigned int)ch
            );
        }
    }

    printf_end("getq");
}

/* Read token. */
next()
{
    printf_start("next");

    int t, l, a;

    /* While current character is id character or `#`. */
    while (isspace(ch) | ch == '#') {
        /* If current character is `#`, it means preprocessing directive. */
        if (ch == '#') {
            /* Read character. */
            inp();

            /* Read token */
            next();

            /* If current token is `define`. */
            if (tok == TOK_DEFINE) {
                /* Parse macro name. */
                next();

                /* Push start marker for macro value to symbol stack. */
                pdef(TAG_TOK); /* fill last ident tag */

                /* Set `vars` table entry's type for macro name.
                ** At 6LRPQ, `tok` is pointed to the table entry. */
                *(int *)tok = SYM_DEFINE;

                /* Store macro value string's symbol stack slot pointer.
                ** The string will be filled below. */
                *(int *)(tok + 4) = dstk; /* define stack */
            }

            /* well we always save the values ! */
            /* While newline is not met. */
            while (ch != '\n') {
                /* Push character to symbol stack. */
                pdef(ch);

                /* Read character. */
                inp();
            }

            /* Push newline to symbol stack. */
            pdef(ch);

            /* 2R6C0
            ** Push macro value's end marker to symbol stack. */
            pdef(TAG_MACRO);
        }

        /* Read character. */
        inp();
    }

    /* Clear operator precedence. */
    tokl = 0;

    /* Store current character. */
    tok = ch;
    /* encode identifiers & numbers */

    printf_text("tok1: 0x%08x `%c`\n", (unsigned int)tok, tok);

    /* If current character is id character,
    ** then the token may be a number or a name. */
    if (isid()) {
        printf_text("branch01: current character is id\n");

        /* Push start marker to symbol stack. */
        pdef(TAG_TOK);

        /* Store the starting character's symbol stack slot pointer. */
        last_id = dstk;

        /* While current character is id character. */
        while (isid()) {
            /* Push current character to symbol stack. */
            pdef(ch);

            /* Read character. */
            inp();
        }

        printf_text("last_id: `%s`\n", last_id);

        /* If the starting character is a digit. */
        if (isdigit(tok)) {
            printf_text("branch02: starting character is digit\n");

            /* Set token value by converting the string to int. */
            tokc = strtol(last_id, 0, 0);

            printf_text("tokc1: 0x%08x\n", (unsigned int)tokc);

            /* Set token type. */
            tok = TOK_NUM;

            printf_text("tok2: 0x%08x\n", (unsigned int)tok);
        } else {
            /* If the starting character is not a digit.
            ** Assume the token is a name symbol. */

            printf_text("branch03: starting character is not digit\n");

            /* Set symbol stack top slot be `TAG_TOK`, so that every name
            ** symbol on symbol stack has left and right `TAG_TOK` marker.
            ** This property is used by the `strstr` search below. */
            *(char *)dstk = TAG_TOK; /* no need to mark end of string (we
                                        suppose data is initied to zero */

            /* Find the symbol name in symbol stack.
            ** Store its offet from the symbol stack bottom to `tok`.
            **
            ** `-1` means to include left marker in order for exact match.
            **
            ** It assumes the name has been declared and pushed to symbol
            ** stack at 5XIHO thus can always be found here. */
            tok = strstr(sym_stk, last_id - 1) - sym_stk;

            printf_text("tok3: 0x%08x\n", (unsigned int)tok);

            /* Restore symbol stack top slot to be '\0'. */
            *(char *)dstk = 0;   /* mark real end of ident for dlsym() */

            /* Compute an offset based on `TOK_IDENT`.
            ** Store the new offset to `tok`.
            ** The offset from the symbol stack bottom in `tok` is used as
            ** index into `vars` table. Each table entry is 8 bytes. */
            tok = tok * 8 + TOK_IDENT;

            printf_text("tok4: 0x%08x\n", (unsigned int)tok);

            /* If the new offset is > `TOK_DEFINE`, then it is not a keyword
            ** (according to the inital value of the symbol stack set at
            ** 7JFQJ), but a user-defined name, including `main`. */
            if (tok > TOK_DEFINE) {
                /* 6LRPQ
                ** Compute an offset based on `vars`.
                ** LHS `tok` points to the name's `vars` table entry. */
                tok = vars + tok;

                printf_text("vars: 0x%08x\n", (unsigned int)vars);

                printf_text("tok5: 0x%08x\n", (unsigned int)tok);

                /*        printf("tok=%s %x\n", last_id, tok); */

                /* define handling */
                /* If the `vars` table entry's type is macro name. */
                if (*(int *)tok == SYM_DEFINE) {
                    /* Store the macro value's symbol stack slot pointer to `dptr`.
                    ** `inp` will read character from the macro value instead.
                    ** This implements macro substitution. */
                    dptr = *(int *)(tok + 4);

                    /* Store the current character because `inp` will read from
                    ** the macro value instead. `ch` will be restored at 7TXIG
                    ** when reading from the macro value is done. */
                    dch = ch;

                    /* Read character. */
                    inp();

                    /* Read token. */
                    next();
                }
            }
        }
    } else {
        /* If current character is not id character,
        ** then it may be character constant, comments, or operator. */

        printf_text("branch04: current character is not id\n");

        /* Read character. */
        inp();

        /* If current character is `'`,
        ** then it is character constant. */
        if (tok == '\'') {
            printf_text("branch05: current character is `'`\n");

            /* Store the token type.
            ** Character constant is treated as number. */
            tok = TOK_NUM;

            printf_text("tok6: 0x%08x\n", (unsigned int)tok);

            /* Read escaped character if any. */
            getq();

            /* Store the character value as associated value. */
            tokc = ch;

            printf_text("tokc2: 0x%08x\n", (unsigned int)tokc);

            /* Read ending `'`. */
            inp();

            /* Read character.
            ** Ignore ending `'`. */
            inp();
        } else if (tok == '/' & ch == '*') {
            /* If it is `/``*`, then it is comments. */

            printf_text("branch06: current character is `/``*`\n");

            /* Read character. */
            inp();

            /* While ending `*``/` is not met. */
            while (ch) {
                /* While current character is not `*`. */
                while (ch != '*')
                    /* Read character. */
                    inp();

                /* Read character. */
                inp();

                /* If current character is `/`, then ending `*``/` is met. */
                if (ch == '/')
                    /* Indicate ending `*``/` is met. */
                    ch = 0;
            }

            /* Read character. */
            inp();

            /* Read token. */
            next();
        } else
        {
            /* If current character is not id, character constant, or comments,
            ** assume it is operator. */

            printf_text("branch07: current character is operator\n");

            /* 3XKZ7
            ** Find `tokl` and `tokc` for the operator. */

            printf_text_v2("Find `tokl` and `tokc` for the operator\n");

            /*  "++  --   *      /        %        +     -        <<     >>     <=  >=  <   >   ==  !=   && ||  &     ^     |     ~     !     */
            t = "++#m--%am*@R<^1c/@%[_[H3c%@%[_[H3c+@.B#d-@%:_^BKd<<Z/03e>>`/03e<=0f>=/f<@.f>@1f==&g!=\'g&&k||#l&@.BCh^@.BSi|@.B+j~@/%Yd!@&d*@b";

            int base;
            base = t;

            /* Get operator token from string `t`. */
            while (l = *(char *)t++) {
                printf_text_v2("Step 1\n");

                printf_text_v2("t: %d\n", t - 1 - base);

                printf_text_v2("l: %x, `%c`\n", l, l);

                /* Get expected following token from string `t`. */
                a = *(char *)t++;

                printf_text_v2("a: %x, `%c`\n", a, a);

                /* Clear associated value. */
                tokc = 0;

                printf_text_v2("Step 2\n");

                /* 6LOQX
                ** This loop's purpose is to set `tokl` and `tokc`'s value for
                ** the operator. For each type of operator, `tokl` and `tokc`'s
                ** value is actually fixed:
                ** Operator: `tokl`, `tokc`
                ** *:   1, 0x00c1af0f
                ** /:   1, 0xf9f79991
                ** %:   1, 0xf9f79991
                ** +:   2, 0x0000c801
                ** -:   2, 0xd8f7c829
                ** ~:   2, 0x0000d0f7
                ** !:   2, 0x00000004
                ** <<:  3, 0x00e0d391
                ** >>:  3, 0x00f8d391
                ** <=:  4, 0x0000000e
                ** >=:  4, 0x0000000d
                ** <:   4, 0x0000000c
                ** >:   4, 0x0000000f
                ** ==:  5, 0x00000004
                ** !=:  5, 0x00000005
                ** &:   6, 0x0000c821
                ** ^:   7, 0x0000c831
                ** |:   8, 0x0000c809
                ** &&:  9, 0x00000000
                ** ||:  10, 0x00000001
                ** ++:  11, 0x00000001
                ** --:  11, 0x000000ff */
                while ((tokl = *(char*)t++ - 'b') < 0) {
                    printf_text_v2("t: %d\n", t - 1 - base);

                    printf_text_v2(
                        "c: `%c`, %d\n",
                        *((char*)t-1), *((char*)t - 1)
                    );

                    tokc = tokc * 64 + tokl + 64;

                    printf_text_v2("tokl: %d\n", tokl);

                    printf_text_v2("tokc: %08x\n", tokc);
                }

                printf_text_v2("t after loop: %d\n", t - base);
                printf_text_v2("tokl after loop: %d\n", tokl);
                printf_text_v2("tokc after loop: 0x%08x\n", tokc);

                printf_text_v2("Step 3\n");

                /* If current token is met and (expected following token is met
                ** or following token does not matter). */
                if (l == tok & (a == ch | a == '@')) {
#if 0
                    printf("%c%c -> tokl=%d tokc=0x%x\n",
                           l, a, tokl, tokc);
#endif
                    /* If expected following token is met, then it is double
                    ** tokens, e.g. `++`. */
                    if (a == ch) {
                        /* Read character. */
                        inp();

                        /* Set current token be dummy token. */
                        tok = TOK_DUMMY; /* dummy token for double tokens */

                        printf_text("tok7: 0x%08x\n", (unsigned int)tok);
                    }

                    printf_text_v2("Found\n");

                    break;
                }
            }

            printf_text_v2("Finding ended. \n");
        }
    }
#if 0
    {
        int p;

        printf("tok=0x%x ", tok);
        if (tok >= TOK_IDENT) {
            printf("'");
            if (tok > TOK_DEFINE)
                p = sym_stk + 1 + (tok - vars - TOK_IDENT) / 8;
            else
                p = sym_stk + 1 + (tok - TOK_IDENT) / 8;
            while (*(char *)p != TAG_TOK && *(char *)p)
                printf("%c", *(char *)p++);
            printf("'\n");
        } else if (tok == TOK_NUM) {
            printf("%d\n", tokc);
        } else {
            printf("'%c'\n", tok);
        }
    }
#endif

    printf_text("ch6: 0x%02x, `%c`\n", (unsigned int)ch, (unsigned int)ch);
    printf_text("tok8: 0x%08x `%c`\n", (unsigned int)tok, tok);
    printf_text("tokl: %d\n", tokl);
    printf_text("tokc3: 0x%08x\n", (unsigned int)tokc);

    printf_end("next");
}

#ifdef TINY
#define skip(c) next()
#else

/* Print error message and exit program. */
void error(char *fmt,...)
{
    va_list ap;

    va_start(ap, fmt);
    fprintf(stderr, "%d: ", ftell((FILE *)file));
    vfprintf(stderr, fmt, ap);
    fprintf(stderr, "\n");
    exit(1);
    va_end(ap);
}

/* Skip expected current token type and read next token.
** `c`: Expected current token type. */
void skip(c)
{
    /* If current token is not the expected type. */
    if (tok != c) {
        /* Print error message and exit program. */
        error("'%c' expected", c);
    }

    /* Read token. */
    next();
}

#endif

/* Add variable-length bytes to instruction buffer's current location.
** `n`: Variable-length bytes in int. */
/* from 0 to 4 bytes */
o(n)
{
    printf_start("o");

    printf_text("%08x: ", ind - prog);

    /* cannot use unsigned, so we must do a hack */
    /* While have remaining bytes. */
    while (n && n != -1) {
        printf_text("%02x", (unsigned char)n);

        /* Add one byte to instruction buffer's current location. */
        *(char *)ind++ = n;

        /* Get next byte. */
        n = n >> 8;
    }

    printf_text("\n");

    printf_end("o");
}

#ifdef ELFOUT

/* put a 32 bit little endian word 'n' at unaligned address 't' */
/* `t`: Address to put value to. */
/* `n`: Value to put to address. */
put32(t, n)
{
    printf_start("put32");

    /* Put 1st byte to the address. */
    *(char *)t++ = n;

    /* Put 2nd byte to the address. */
    *(char *)t++ = n >> 8;

    /* Put 3rd byte to the address. */
    *(char *)t++ = n >> 16;

    /* Put 4th byte to the address. */
    *(char *)t++ = n >> 24;

    printf_text(
        "%08x: %02x%02x%02x%02x\n",
        ind - prog,
        (unsigned char)n,
        (unsigned char)n >> 8,
        (unsigned char)n >> 16,
        (unsigned char)n >> 24
    );

    printf_end("put32");
}

/* get a 32 bit little endian word at unaligned address 't' */
/* `t`: Address to get value from. */
get32(t)
{
    int n;
    return  (*(char *)t & 0xff) |
        (*(char *)(t + 1) & 0xff) << 8 |
        (*(char *)(t + 2) & 0xff) << 16 |
        (*(char *)(t + 3) & 0xff) << 24;
}

#else

#define put32(t, n) *(int *)t = n
#define get32(t) *(int *)t

#endif

/* Patch a chain of pending address fields to hold target address.
** `t`: A head pointer to a chain of pending address fields to be patched.
** See 5YPXH for the pending address fields chaining mechanism.
** `b`: Target address. */
/* output a symbol and patch all references to it */
gsym1(t, b)
{
    printf_start("gsym1");

    int n;

    /* While end-of-chain marker 0 is not met. */
    while (t) {
        /* Get next address field's pointer. */
        n = get32(t); /* next value */

        /* patch absolute reference (always mov/lea before) */
        /* If the patched address field is absolute address. */
        if (*(char *)(t - 1) == 0x05) {
            /* XXX: incorrect if data < 0 */
            /* If the target address is within data segment. */
            if (b >= data && b < glo)
                /* Put final address to the address field. */
                put32(t, b + data_offset);
            else
                /* If the target address is not within data segment. */

                /* Put final address to the address field. */
                put32(t, b - prog + text + data_offset);
        } else {
            /* If the patched address field is relative address. */

            printf_text("Jump address field: %x\n", t - prog);
            printf_text("Jump offset base: %x\n", t + 4 - prog);
            printf_text("Jump offset: %x\n", b - t - 4);
            printf_text("Jump target: %x\n", b - prog);

            /* Put final address to the address field.
            ** `- 4` means the offset base is the address of the instruction
            ** after the jump address field. */
            put32(t, b - t - 4);
        }

        /* To patch next pending address field. */
        t = n;
    }

    printf_end("gsym1");
}

/* Patch a chain of pending address fields to hold instruction buffer's current
** location's address.
** `t`: A head pointer to a chain of pending address fields to be patched.
** See 5YPXH for the pending address fields chaining mechanism of `t`. */
gsym(t)
{
    gsym1(t, ind);
}

/* psym is used to put an instruction with a data field which is a
   reference to a symbol. It is in fact the same as oad ! */
#define psym oad

/* Generate instruction with address field.
** `n`: Opcode bytes to add to instruction buffer.
** `t`: Address bytes to add to instruction buffer. */
/* instruction + address */
oad(n, t)
{
    printf_start("oad");

    /* Add opcode bytes in `n` to instruction buffer. */
    o(n);

    /* 5YPXH
    ** Add the address in `t` to instruction buffer.
    ** This creates an address field, e.g. for jump instruction.
    **  */
    put32(ind, t);

    /* Store the address field's pointer in `t`.
    ** This is the new head pointer to the chain of pending address fields to
    ** be patched later. */
    t = ind;

    /* Increase instruction buffer's current location pointer. */
    ind = ind + 4;

    printf_end("oad");

    /* Return pointer to the address field. */
    return t;
}

/* Generate instruction to move immediate value to %eax.
** `t`: Immediate value. */
/* load immediate value */
li(t)
{
    printf_start("li");

    /* Generate instruction to move immediate value to %eax.
    ** 0xb8XXXXXXXX: mov $0xXXXXXXXX, %eax. */
    oad(0xb8, t); /* mov $xx, %eax */

    printf_end("li");
}

/* Generate jump instruction.
** `t`: Jump address.
** See 5YPXH for the pending address fields chaining mechanism. */
gjmp(t)
{
    int res;

    printf_start("gjmp");

    /* Generate jump instruction.
    ** e9XXXXXXXX: jmp %ip+XXXXXXXX*/
    res = psym(0xe9, t);

    printf_end("gjmp");

    /* Return pointer to the address field. */
    return res;
}

/* Generate instructions to test whether the test expression's value in %eax is
** 0, and jump based on this.
** `t`: Jump address.
** See 5YPXH for the pending address fields chaining mechanism of `t`. */
/* l = 0: je, l == 1: jne */
gtst(l, t)
{
    int res;

    printf_start("gtst");

    /* Generate instruction to test whether %eax is 0.
    ** 85c0: test %eax, %eax */
    o(0x0fc085); /* test %eax, %eax, je/jne xxx */

    /* Generate jump instruction.
    ** 0f84: je
    ** 0f85: jne */
    res = psym(0x84 + l, t);

    printf_end("gtst");

    /* Return pointer to the address field. */
    return res;
}

/* Generate instructions to do logical comparison.
** `t`: Determine the `setXX` instruction type. */
gcmp(t)
{
    printf_start("gcmp");

    /* Generate instruction to compare %eax and %ecx.
    ** 39c1: cmp %eax, %ecx. */
    o(0xc139); /* cmp %eax,%ecx */

    /* Generate instruction to move 0 to %eax. */
    li(0);

    /* Put the comparison's result value to %al.
    ** The comparison mode is determined by `t`, e.g.:
    ** 0f90c0: seto %al
    ** 0f91c0: setno %al
    ** 0f92c0: setb %al
    ** 0f93c0: setae %al
    ** 0f94c0: sete %al */
    o(0x0f); /* setxx %al */
    o(t + 0x90);
    o(0xc0);

    printf_end("gcmp");
}

/* Generate various instructions. */
gmov(l, t)
{
    printf_start("gmov");

    int n;

    /* Generate instruction.
    ** 0x83 + 0 = 0x83, starting bytes for instruction `add $X, -X(%ebp)`
    ** 0x83 + 6 = 0x89, starting bytes for instruction `mov %eax, _ADDR_`.
    ** 0x83 + 8 = 0x8b, starting bytes for instruction `mov _ADDR_, %eax`.
    ** 0x83 + 10 = 0x8d, starting bytes for instruction `lea`. */
    o(l + 0x83);

    /* Get `vars` table entry's value. */
    n = *(int *)t;

    /* If n < `LOCAL`, it is local variable's stack offset. */
    if (n && n < LOCAL)
        /* 6KHU8
        ** E.g. 8385fcffffff: add $1, -4(%ebp)
        ** E.g. 8d85fcffffff: lea -4(%ebp), %eax */
        oad(0x85, n);
    else {
        /* If n >= `LOCAL`, it is a name symbol. */

        /* Get head pointer to a chain of pending address fields for the
        ** symbol. */
        t = t + 4;

        /* Generate address field to hold the name's address.
        ** See 5YPXH for the pending address fields chaining mechanism of
        ** `*(int *)t`. */
        *(int *)t = psym(0x05, *(int *)t);
    }

    printf_end("gmov");
}

/* Parse unary expression. */
/* l is one if '=' parsing wanted (quick hack) */
unary(l)
{
    printf_start("unary");
    printf_text("l: %d\n", l);
    printf_text("tok: %d `%c`\n", tok, tok);
    printf_text("tokl: %d\n", tokl);
    printf_text("tokc: %08x\n", tokc);

    int n, t, a, c;

    n = 1; /* type of expression 0 = forward, 1 = value, other =
              lvalue */

    /* If current token is `"`, it means string constant. */
    if (tok == '\"') {
        printf_text("branch08: current token is `\"`\n");

        /* Generate instruction to load the constant string's starting address
        ** to %eax. */
        li(glo + data_offset);

        /* While ending `"` is not met. */
        while (ch != '\"') {
            /* Read escaped character if any. */
            getq();

            /* Store current character in data segment buffer. */
            *(char *)glo++ = ch;

            /* Read character. */
            inp();
        }

        /* Store ending '\0' in data segment buffer. */
        *(char *)glo = 0;

        /* Increase `glo` to next 4-byte aligned address.
        ** `-4` is 0x11111100. */
        glo = glo + 4 & -4; /* align heap */

        /* Read character. */
        inp();

        /* Read token. */
        next();
    } else {
        /* If current token is not `"`. */

        printf_text("branch09: current token is not `\"`\n");

        /* Store current operator precedence.
        ** `tokl` and `tokc` are determined at 6LOQX. */
        c = tokl;

        /* Store current token's associated value. */
        a = tokc;

        /* Store current token type. */
        t = tok;

        /* Read token. */
        next();

        /* If pending token is number. */
        if (t == TOK_NUM) {
            printf_text("branch10: pending token is number\n");

            /* Generate instruction to move the number to %eax. */
            li(a);
        } else if (c == 2) {
            /* 6DQTG
            ** If pending operator precedence is 2, then it is prefix operator.
            ** Operator: `tokl`, `tokc`
            ** +:   2, 0x0000c801
            **         (01c8) addl% ecx, % eax
            ** -:   2, 0xd8f7c829
            **         (29c8) subl %ecx, %eax
            **         (f7d8) negl %eax
            ** ~:   2, 0x0000d0f7
            **         (f7d0) notl %eax
            ** !:   2, 0x00000004
            **         (39c1) cmpl %eax, %ecx
            **         (b800000000) movl $0, %eax
            **         (0f94c0) sete %al
            */

            printf_text("branch11: pending operator precedence is 2\n");

            /* -, +, !, ~ */
            /* Parse operand.
            ** Result value after execution will be put to %eax. */
            unary(0);

            /* Generate instruction to move 0 to %ecx.
            ** b900000000: movl $0, %ecx.
            ** %ecx is used in `gcmp` below. */
            oad(0xb9, 0); /* movl $0, %ecx */

            /* If pending operator is negate operator. */
            if (t == '!')
                /* Generate instructions to put negated value to %eax. */
                gcmp(a);
            else
                /* Generate instruction in the operator's associated value. */
                o(a);
        } else if (t == '(') {
            /* If pending token is `(`, then it is expression in brackets. */

            printf_text("branch12: pending token is `(`\n");

            /* Parse expression.
            ** Result value after execution will be put to %eax. */
            expr();

            /* Skip ending `)` and read token. */
            skip(')');
        } else if (t == '*') {
            /* If pending token is `*`, then it is dereference operator. */

            printf_text("branch13: pending token is `*`\n");

            /* parse cast */
            /* Skip cast's starting `(` and read token.
            ** The syntax requires dereference operator be followed by cast. */
            skip('(');

            /* Store cast's base type. */
            t = tok; /* get type */

            /* Read token. */
            next(); /* skip int/char/void */

            /* Skip `*` or `(`. */
            next(); /* skip '*' or '(' */

            /* If current token is `*`, then it is cast to function pointer,
            ** e.g. `(int(*` followed by `)())`. */
            if (tok == '*') {
                /* function type */
                /* Skip characters. */
                skip('*');
                skip(')');
                skip('(');
                skip(')');

                /* Indicate it is cast to function pointer. */
                t = 0;
            }

            /* Skip cast's ending `)` and read token. */
            skip(')');

            /* Parse casted expression.
            ** Result value after execution will be put to %eax. */
            unary(0);

            /* If current token is `=`, then it is assignment to dereferenced
            ** pointer, e.g. `*(int*)p = 1`. */
            if (tok == '=') {
                /* Read token. */
                next();

                /* Generate instruction to push LHS address value in %eax. */
                o(0x50); /* push %eax */

                /* Parse RHS expression.
                ** Result value after execution will be put to %eax. */
                expr();

                /* Generate instruction to pop LHS address value to %ecx. */
                o(0x59); /* pop %ecx */

                /* Generate instruction to move RHS value in %eax to LHS
                ** address in %ecx.
                ** 8801: movb %al, 0(%ecx).
                ** 8901: mov %eax, 0(%ecx). */
                o(0x0188 + (t == TOK_INT)); /* movl %eax/%al, (%ecx) */
            } else if (t) {
                /* If current token is not `=`, and is not cast to function
                ** pointer. */

                /* If cast's base type is `int`. */
                if (t == TOK_INT)
                    /* Generate instruction to move dereferenced int value to %eax.
                    /* `*(int*)p`: 8b00: movl 0(%eax), %eax. */
                    o(0x8b); /* mov (%eax), %eax */
                else
                    /* If cast's base type is not `int`.
                    ** Assume it is `char`. */

                    /* Generate instruction to move dereferenced char value to %eax.
                    ** `*(char*)p`: 0fbe00: movsb 0(%eax), %eax. */
                    o(0xbe0f); /* movsbl (%eax), %eax */

                /* Add 0x00 to instruction buffer. */
                ind++; /* add zero in code */
            }
        } else if (t == '&') {
            /* If pending token is `&`, then it is address-of operator. */

            printf_text("branch14: pending token is `&`\n");

            /* Generate instruction to load the operand's address to %eax.
            ** `10` plus 0x83 in `gmov` gets 0x8d, which is starting bytes
            ** for instruction `lea`.
            ** `tok` points to `vars` table entry of the operand. */
            gmov(10, tok); /* leal EA, %eax */

            /* Read token. */
            next();
        } else {
            /* If pending token is not number, prefix operator, bracket,
            ** dereference operator, address-of operator, then assume it is a
            ** name symbol. */

            printf_text("branch15: else\n");

            /* Indicate pending token is a name symbol. */
            n = 0;

            /* If current token is `=`, and parsing assignment is wanted. */
            if (tok == '=' & l) {
                printf_text("branch16: token is `=` and `=` parsing is wanted\n");

                /* assignment */
                /* Read token. */
                next();

                /* Parse RHS expression.
                ** Result value after execution will be put to %eax. */
                expr();

                /* Generate instruction to move RHS value in %eax to LHS.
                ** `6` plus 0x83 in `gmov` gets 0x89, which is starting bytes
                ** for instruction `mov %eax, _ADDR_`.
                ** `t` points to `vars` table entry of the LHS name symbol. */
                gmov(6, t); /* mov %eax, EA */
            } else if (tok != '(') {
                /* If current token is not `(`, i.e. it is not function call,
                ** then it should be a lower-precedence operator that is not
                ** handled here so simply load the LHS variable's value. */

                printf_text("branch17: token is not `(`\n");

                /* variable */
                /* Generate instruction to move variable value to %eax.
                ** `8` plus 0x83 in `gmov` gets 0x8b, which is starting bytes
                ** for instruction `mov _ADDR_, %eax`.
                ** `t` points to `vars` table entry of the name symbol. */
                gmov(8, t); /* mov EA, %eax */

                /* 5MPX5
                ** If current token is postfix operator `++` or `--`.
                ** Operator: tokl, tokc
                ** ++:  11, 0x00000001
                ** --:  11, 0x000000ff */
                if (tokl == 11) {
                    /* The variable's current value is in %eax.
                    ** The incremented or decremented value will be put tp
                    ** memory. So the postfix semantics is implemented. */

                    /* Generate `add` instruction `add $X, _ADDR_`. */
                    gmov(0, t);

                    /* Generate immediate value `$X` for the `add` instruction
                    ** above.
                    ** 0x01 ($1) for `++`.
                    ** 0xFF ($-1) for `--`. */
                    o(tokc);

                    /* Read token. */
                    next();
                }
            }
        }
    }

    /* function call */
    /* If current token is `(`, then it is function call. */
    if (tok == '(') {
        /* If called expression is not a function name,
        ** then the function address is the current value in %eax. */
        if (n)
            /* Generate instruction to push the function address in %eax. */
            o(0x50); /* push %eax */

        /* push args and invert order */
        /* Generate instruction to move stack top pointer downwards, reserving
        ** stack slots for the function call's arguments.
        ** 81ec00000000: sub $0, %esp.
        ** `a` points to the immediate value field to be patched later, as the
        ** number of arguments is unknown at this point. */
        a = oad(0xec81, 0); /* sub $xxx, %esp */

        /* Read token. */
        next();

        /* Current argument's stack offset. */
        l = 0;

        /* While arguments list's ending `)` is not met. */
        while(tok != ')') {
            /* Parse argument's expression.
            ** Result value after execution will be put to %eax. */
            expr();

            /* Generate instruction to move the argument's result value to the
            ** stack slot reserved for it above.
            ** 898424XXXXXX: mov %eax, 0xXXXXXX(%esp). */
            oad(0x248489, l); /* movl %eax, xxx(%esp) */

            /* If current token is `,`.
            ** `,` is optional in the syntax. */
            if (tok == ',')
                /* Read token. */
                next();

            /* Get next argument's stack offset. */
            l = l + 4;
        }

        /* Patch the immediate value in the instruction above. */
        put32(a, l);

        /* Read token. */
        next();

        /* If called expression is not a function name,
        ** then the function address in %eax has been pushed to stack. */
        if (n) {
            /* Generate call instruction.
            ** ff9424XXXXXX: call *XXXXXX(%esp)
            */
            oad(0x2494ff, l); /* call *xxx(%esp) */

            /* Add 4 to pop off the function address besides arguments. */
            l = l + 4;
        } else {
            /* If called expression is a function name. */

            /* forward reference */

            /* Get pointer to the function address. */
            t = t + 4;

            /* Generate call instruction.
            ** e8XXXXXXXX: call XXXXXXXX.
            ** See 5YPXH for the pending address fields chaining mechanism of
            ** `*(int *)t`. */
            *(int *)t = psym(0xe8, *(int *)t);
        }

        /* If have arguments or the function address is on stack. */
        if (l)
            /* Generate instruction to move stack top pointer upwards, popping
            ** arguments and function address off stack.
            ** 81c4XXXXXXXX: add $XXXXXXXX, %esp. */
            oad(0xc481, l); /* add $xxx, %esp */
    }

    printf_end("unary");
}

/* Parse binary operator expression.
** `sum` implements operator precedence climbing using recursion.
** Lower-precedence operators wait for higher-precedence operators
** to finish parsing.
** See 6LOQX for operator precedence list.
** `l`: Current operator precedence. */
sum(l)
{
    printf_start("sum");
    printf_text("l: %d\n", l);
    printf_text("tok: %d `%c`\n", tok, tok);
    printf_text("tokl: %d\n", tokl);
    printf_text("tokc: %08x\n", tokc);

    int t, n, a;

    /* If current operator precedence is 1. */
    if (l-- == 1)
        /* Parse LHS unary expression. */
        unary(1);
    else {
        /* If current operator precedence is not 1. */

        /* 6ZII9
        ** Parse LHS higher-precedence-operator expression. `sum(l)` and its
        ** recursive calls will keep parsing until a lower-precedence operator
        ** is met with which they can not proceed. */
        sum(l);

        /* At this point the current token is a lower-precedence operator the
        ** `sum(l)` above can not handle. */

        /* Clear `a`. */
        a = 0;

        /* While current token is an operator that should be handled in current
        ** precedence. E.g. this implements the `('+' term)*` part in BNF rule
        ** `term ('+' term)*`. */
        while (l == tokl) {
            /* Store current operator token. */
            n = tok;

            /* Store current operator's associated value.
            ** The associated value determines opcode generated below. */
            t = tokc;

            /* Read token. */
            next();

            /* If operator precedence > 8.
            **
            ** Operator: `tokl`, `tokc`
            ** &&:  9, 0x00000000
            ** ||:  10, 0x00000001
            **
            ** Precedence 11 (`++` and `--`) is handled in `unary` at 5MPX5, so
            ** will not be met here unless used as binary operator erroneously.
            */
            if (l > 8) {
                /* Generate instructions to test current value in %eax and jump
                ** to end of the whole logical expression if short circuit is
                ** triggered.
                **
                ** `t` determines whether the instruction is `je` or `jne`.
                ** For `&&` it is `je` because false value triggers
                ** short-circuit, so `tokc` is 0.
                ** For `||` it is `jne` because true value triggers
                ** short-circuit, so `tokc` is 1.
                **
                ** See 5YPXH for the pending address fields chaining mechanism
                ** of `a`. */
                a = gtst(t, a); /* && and || output code generation */

                /* Parse RHS expression. */
                sum(l);
            } else {
                /* If operator precedence <= 8. */

                /* Push LHS expression's value in %eax */
                o(0x50); /* push %eax */

                /* Parse RHS expression.
                /* Result value after execution will be put to %eax. */
                sum(l);

                /* Pop LHS expression's value to %ecx */
                o(0x59); /* pop %ecx */

                /* At this point, LHS is in %ecx, RHS is in %eca. */

                /* If operator precedence is 4 or 5.
                **
                ** Operator: `tokl`, `tokc`
                ** <=:  4, 0x0000000e
                ** >=:  4, 0x0000000d
                ** <:   4, 0x0000000c
                ** >:   4, 0x0000000f
                ** ==:  5, 0x00000004
                ** !=:  5, 0x00000005 */
                if (l == 4 | l == 5) {
                    /* Generate instructions to do logical comparison.
                    ** Result value after execution will be put to %eax. */
                    gcmp(t);
                } else {
                    /* If operator precedence is 1, 2, 3, 6, 7, 8.
                    **
                    ** Prefix operators `~` and `!` are handled in `unary` at
                    ** 6DQTG so will not be met here unless used as binary
                    ** operator erroneously.
                    **
                    ** Operator: `tokl`, `tokc`
                    ** *:   1, 0x00c1af0f
                    **         (0fafc1) imull %ecx, %eax
                    ** /:   1, 0xf9f79991
                    ** %:   1, 0xf9f79991
                    **         (91) xchgl % ecx, % eax
                    **         (99) cltd
                    **         (f7f9) idivl % ecx
                    ** +:   2, 0x0000c801
                    **         (01c8) addl %ecx, %eax
                    ** -:   2, 0xd8f7c829
                    **         (29c8) subl %ecx, %eax
                    **         (f7d8) negl %eax
                    ** ~:   2, 0x0000d0f7 (syntax error)
                    ** !:   2, 0x00000004 (syntax error)
                    ** <<:  3, 0x00e0d391
                    **         (91) xchgl % ecx, % eax
                    **         (d3e0) shll % cl, % eax
                    ** >>:  3, 0x00f8d391
                    **         (91) xchgl % ecx, % eax
                    **         (d3f8): sarl % cl, % eax
                    ** &:   6, 0x0000c821
                    **         (21c8) andl % ecx, % eax
                    ** ^:   7, 0x0000c831
                    **         (31c8) xorl %ecx, %eax
                    ** |:   8, 0x0000c809
                    **         (09c8) orl %ecx, %eax */

                    /* Use the operator token's associated value to generate
                    ** instruction. */
                    o(t);

                    /* If the operator token is `%`. */
                    if (n == '%') {
                        /* Generate instruction. */
                        o(0x92); /* xchg %edx, %eax */
                    }
                }
            }
        }

        /* && and || output code generation */
        /* Convert to 0 or 1 in the end of the whole logical expression.
        ** Unlike bitwise, logical AND/OR expression only computes boolean
        ** result in the end.
        **
        ** Operator: `tokl`, `tokc`
        ** &&:  9, 0x00000000
        ** ||:  10, 0x00000001 */
        if (a && l > 8) {
            /* Generate instruction to test and jump to branch B below. */
            a = gtst(t, a);

            /* Generate instruction to move 0 or 1 to %eax.
            ** This is branch A. */
            li(t ^ 1);

            /* Generate instruction at end of branch A to jump to end of branch
            ** B. */
            gjmp(5); /* jmp $ + 5 */

            /* Patch the chain of pending address fields pointed to by `a` to
            ** hold instruction buffer's current address. */
            gsym(a);

            /* Generate instruction to move 1 or 0 to %eax.
            ** This is branch B. */
            li(t);
        }
    }

    printf_end("sum");
}

/* Parse expression. */
expr()
{
    printf_start("expr");
    printf_text("tok: %d `%c`\n", tok, tok);
    printf_text("tokl: %d\n", tokl);
    printf_text("tokc: %08x\n", tokc);

    /* Parse binary expression with the lowest operator precedence.
    ** Greater number means lower precedence. */
    sum(11);

    printf_end("expr");
}

/* Parse test expression.
** See 5YPXH for the pending address fields chaining mechanism. */
test_expr()
{
    int res;

    printf_start("test_expr");

    /* Parse expression. */
    expr();

    /* Generate test and jump instructions. */
    res = gtst(0, 0);

    printf_end("test_expr");

    /* Return pointer to the address field. */
    return res;
}

/* Parse block.
** `l`: Pointer to head pointer to a chain of pending `break` jump address
** fields.
** Use pointer to pointer because need to change the head pointer's value in
** the callee and use the new value in the caller.
** See 5YPXH for the pending address fields chaining mechanism. */
block(l)
{
    printf_start("block");
    printf_text("l: %d\n", l);

    int a, n, t;

    /* If current token is `if`. */
    if (tok == TOK_IF) {
        /* Parse `(`. */
        next();

        /* Skip `(` and read token. */
        skip('(');

        /* The true branch comes after the test expression.
        ** The false branch comes after the true branch so needs jump.
        ** `a` points to the jump instruction's address field for the false
        ** branch. */
        a = test_expr();

        /* Skip `)` and read token. */
        skip(')');

        /* Parse true branch. */
        block(l);

        /* If have else branch, else branch follows the true branch, so there
        ** needs a jump after the true branch to jump over the else branch. */
        if (tok == TOK_ELSE) {
            /* Read `{`. */
            next();

            /* Add jump instruction after the true branch to jump over the else
            ** branch.
            ** `n` points to the jump address field. */
            n = gjmp(0); /* jmp */

            /* Patch `a` to hold the address of the else branch. */
            gsym(a);

            /* Parse false branch. */
            block(l);

            /* Patch `n` to hold the address after the else branch. */
            gsym(n); /* patch else jmp */
        } else {
            /* Patch `a` to hold the address of the false branch, i.e. after
            ** the true branch. */
            gsym(a); /* patch if test */
        }
    } else if (tok == TOK_WHILE | tok == TOK_FOR) {
        /* If current token is `while` or `for`. */

        /* Store current token. */
        t = tok;

        /* Read `(`. */
        next();

        /* Skip `(` and read token. */
        skip('(');

        /* If current token is `while`. */
        if (t == TOK_WHILE) {
            /* Store address of the loop's test expression. */
            n = ind;

            /* Parse test expression.
            ** The true branch comes after the test expression.
            ** The false branch comes after the true branch so needs jump.
            ** `a` points to the jump instruction's address field for the false
            ** branch. */
            a = test_expr();
        } else {
            /* If current token is `for`. */

            /* If current token is not `;`, it means having initialization
            ** expression. */
            if (tok != ';')
                /* Parse initialization expression. */
                expr();

            /* Skip the first `;` and read token. */
            skip(';');

            /* Store test expression's address. */
            n = ind;

            /* `a` points to jump address field for end of loop. */
            a = 0;

            /* If current token is not `;`, it means having test expression. */
            if (tok != ';')
                /* Parse test expression. */
                a = test_expr();

            /* Skip the second `;` and read token. */
            skip(';');

            /* If current token is not `)`, it means having stepping
            ** expression. */
            if (tok != ')') {
                /* Generate jump instruction to jump to loop body because
                ** stepping expression should not be executed before entering
                ** the first round.
                ** `t` points to the jump address field. */
                t = gjmp(0);

                /* Parse stepping expression. */
                expr();

                /* Generate instruction to jump to test expression.
                ** `- 5` counts the jump instruction itself. */
                gjmp(n - ind - 5);

                /* Patch `t` to hold loop body's address. */
                gsym(t);

                /* Store stepping expression's address. */
                n = t + 4;
            }
        }

        /* Skip `)` and read token. */
        skip(')');

        /* Parse loop body. */
        block(&a);

        /* Add instruction to jump to the loop's stepping expression if any, or
        ** test expression if any, or loop body.
        ** `- 5` counts the jump instruction itself. */
        gjmp(n - ind - 5); /* jmp */

        /* Patch `a` to hold the address of the false branch, i.e. after the
        ** loop body. */
        gsym(a);
    } else if (tok == '{') {
        /* If current token is `{`, it is block. */

        /* Read token. */
        next();

        /* declarations */
        /* Parse declaration. */
        decl(1);

        /* While ending `}` is not met. */
        while(tok != '}')
            /* Parse block. */
            block(l);

        /* Skip ending `}`. */
        next();
    } else {
        /* If current token is not `if`, `while`, `for`, block. */

        /* If current token is `return`. */
        if (tok == TOK_RETURN) {
            /* Read token. */
            next();

            /* If current token is not `;`, it means having return value. */
            if (tok != ';')
                /* Parse return expression. */
                expr();

            /* Create jump instruction for the return statement.
            ** See 5YPXH for the pending address fields chaining mechanism of
            ** `rsym`.
            */
            rsym = gjmp(rsym); /* jmp */
        } else if (tok == TOK_BREAK) {
            /* If current token is `break`. */

            /* Read token. */
            next();

            /* Create jump instruction for `break`.
            ** See 5YPXH for the pending address fields chaining mechanism of
            ** `*(int *)l`. */
            *(int *)l = gjmp(*(int *)l);
        } else if (tok != ';')
            /* If current token is not `;`, then assume it is an expression. */

            /* Parse expression. */
            expr();

        /* Skip `;` and read token. */
        skip(';');
    }

    printf_end("block");
}

/* Parse declaration.
/* 'l' is true if local declarations */
decl(l)
{
    printf_start("decl");
    printf_text("l: %d\n", l);
    printf_text("tok: %d `%c`\n", tok, tok);
    printf_text("tokl: %d\n", tokl);
    printf_text("tokc: %08x\n", tokc);

    int a;

    /* While current token is `int` or (is not EOF and is not inside function).
    ** The loop condition means can define variable but can not define function
    ** inside function.
    */
    while (tok == TOK_INT | tok != -1 & !l) {
        /* If current token is `int`. */
        if (tok == TOK_INT) {
            printf_text("branch18: current token is `int`\n");

            /* Read name token.
            ** At 6LRPQ, `tok` is pointed to the name's `vars` table entry. */
            next();

            /* While current token is not `;`. */
            while (tok != ';') {
                /* 5XIHO
                ** If is inside function, then the name is a local vairable
                ** name. */
                if (l) {
                    printf_text("branch19: is inside function\n");

                    /* Get the local variable's stack offset.
                    ** `+ 4`: The first argument is at stack offset -4. */
                    loc = loc + 4;

                    /* Store the local variable's stack offset in the variable
                    ** name's `vars` table entry.
                    **
                    ** The negative offset is used at 6KHU8 as `leal`
                    ** instruction's argument. */
                    *(int *)tok = -loc;
                } else {
                    /* If is not inside function, then the name is a global
                    ** vairable name. */

                    printf_text(
                        "ch2: 0x%02x, `%c`\n",
                        (unsigned int)ch,
                        (unsigned int)ch
                    );

                    /* Store the global variable's address in the variable
                    ** name's `vars` table entry. */
                    *(int *)tok = glo;

                    /* Point to next global variable. */
                    glo = glo + 4;
                }

                /* Read token. */
                next();

                /* If current token is `,`.
                ** `,` is optional in the syntax. */
                if (tok == ',')
                    /* Read token. */
                    next();
            }

            /* Skip `;` and read token. */
            skip(';');
        } else {
            /* If current token is not `int`.
            ** Assume it is function definition. */

            printf_text("branch21: current token is not `int`\n");

            /* put function address */
            /* Store function address in the function name's `vars` table
            ** entry.
            ** At 6LRPQ, `tok` is pointed to the function name's `vars` table
            ** entry.
            */
            *(int *)tok = ind;

            /* Read `(`. */
            next();

            /* Skip `(` and read parameter name. */
            skip('(');

            /* Parameter's offset base. */
            a = 8;

            /* While ending ')' is not met. */
            while (tok != ')') {
                /* read param name and compute offset */

                printf_text("Store parameter offset\n");

                /* Store the parameter's offset in its `vars` table entry. */
                *(int *)tok = a;

                /* Get next parameter's offset. */
                a = a + 4;

                printf_text("Read parameter name\n");

                /* Read `,` or parameter name. */
                next();

                /* If current token is `,`.
                ** `,` is optional in the syntax. */
                if (tok == ',')
                    /* Read parameter name. */
                    next();
            }

            /* Skip ending `)`. */
            next(); /* skip ')' */

            /* Reset for each function definition. */
            rsym = loc = 0;

            /* Generate instructions before function body.
            ** 55: push %ebp
            ** 89e5: mov %esp, %ebp */
            o(0xe58955); /* push   %ebp, mov %esp, %ebp */

            /* 2GK5R
            ** Generate instructions to decrease %esp by $xxx to reserve space
            ** for the call frame.
            ** `a` points to $xxx and will be patched later. */
            a = oad(0xec81, 0); /* sub $xxx, %esp */

            /* Parse function body.
            ** 0 means end marker for a chain of pending break jump address
            ** fields. */
            block(0);

            /* Patch a chain of pending return jump address fields to hold
            ** current address. */
            gsym(rsym);

            /* Generate instructions after function body.
            ** c9: leave: Move %ebp to %esp, pop to %ebp.
            ** c3: ret: Return to the caller's address on stack. */
            o(0xc3c9); /* leave, ret */

            /* Set the $xxx of the instruction created at 2GK5R. */
            put32(a, loc); /* save local variables */
        }
    }

    printf_end("decl");
}

#ifdef ELFOUT

gle32(n)
{
    put32(glo, n);
    glo = glo + 4;
}

/* used to generate a program header at offset 't' of size 's' */
gphdr1(n, t)
{
    gle32(n);
    n = n + ELF_BASE;
    gle32(n);
    gle32(n);
    gle32(t);
    gle32(t);
}

elf_reloc(l)
{
    int t, a, n, p, b, c;

    p = 0;
    t = sym_stk;
    while (1) {
        /* extract symbol name */
        t++;
        a = t;
        while (*(char *)t != TAG_TOK && t < dstk)
            t++;
        if (t == dstk)
            break;
        /* now see if it is forward defined */
        tok = vars + (a - sym_stk) * 8 + TOK_IDENT - 8;
        b = *(int *)tok;
        n = *(int *)(tok + 4);
        if (n && b != 1) {
#if 0
            {
                char buf[100];
                memcpy(buf, a, t - a);
                buf[t - a] = '\0';
                printf("extern ref='%s' val=%x\n", buf, b);
            }
#endif
            if (!b) {
                if (!l) {
                    /* symbol string */
                    memcpy(glo, a, t - a);
                    glo = glo + t - a + 1; /* add a zero */
                } else if (l == 1) {
                    /* symbol table */
                    gle32(p + DYNSTR_BASE);
                    gle32(0);
                    gle32(0);
                    gle32(0x10); /* STB_GLOBAL, STT_NOTYPE */
                    p = p + t - a + 1; /* add a zero */
                } else {
                    p++;
                    /* generate relocation patches */
                    while (n) {
                        a = get32(n);
                        /* c = 0: R_386_32, c = 1: R_386_PC32 */
                        c = *(char *)(n - 1) != 0x05;
                        put32(n, -c * 4);
                        gle32(n - prog + text + data_offset);
                        gle32(p * 256 + c + 1);
                        n = a;
                    }
                }
            } else if (!l) {
                /* generate standard relocation */
                gsym1(n, b);
            }
        }
    }
}

elf_out(c)
{
    int glo_saved, dynstr, dynstr_size, dynsym, hash, rel, n, t, text_size;

    /*****************************/
    /* add text segment (but copy it later to handle relocations) */
    text = glo;
    text_size = ind - prog;

    /* add the startup code */
    ind = prog;
    o(0x505458); /* pop %eax, push %esp, push %eax */
    t = *(int *)(vars + TOK_MAIN);
    oad(0xe8, t - ind - 5);
    o(0xc389);  /* movl %eax, %ebx */
    li(1);      /* mov $1, %eax */
    o(0x80cd);  /* int $0x80 */
    glo = glo + text_size;

    /*****************************/
    /* add symbol strings */
    dynstr = glo;
    /* libc name for dynamic table */
    glo++;
    glo = strcpy(glo, "libc.so.6") + 10;
    glo = strcpy(glo, "libdl.so.2") + 11;

    /* export all forward referenced functions */
    elf_reloc(0);
    dynstr_size = glo - dynstr;

    /*****************************/
    /* add symbol table */
    glo = (glo + 3) & -4;
    dynsym = glo;
    gle32(0);
    gle32(0);
    gle32(0);
    gle32(0);
    elf_reloc(1);

    /*****************************/
    /* add symbol hash table */
    hash = glo;
    n = (glo - dynsym) / 16;
    gle32(1); /* one bucket (simpler!) */
    gle32(n);
    gle32(1);
    gle32(0); /* dummy first symbol */
    t = 2;
    while (t < n)
        gle32(t++);
    gle32(0);

    /*****************************/
    /* relocation table */
    rel = glo;
    elf_reloc(2);

    /* copy code AFTER relocation is done */
    memcpy(text, prog, text_size);

    glo_saved = glo;
    glo = data;

    /* elf header */
    gle32(0x464c457f);
    gle32(0x00010101);
    gle32(0);
    gle32(0);
    gle32(0x00030002);
    gle32(1);
    gle32(text + data_offset); /* address of _start */
    gle32(PHDR_OFFSET); /* offset of phdr */
    gle32(0);
    gle32(0);
    gle32(0x00200034);
    gle32(3); /* phdr entry count */

    /* program headers */
    gle32(3); /* PT_INTERP */
    gphdr1(INTERP_OFFSET, INTERP_SIZE);
    gle32(4); /* PF_R */
    gle32(1); /* align */

    gle32(1); /* PT_LOAD */
    gphdr1(0, glo_saved - data);
    gle32(7); /* PF_R | PF_X | PF_W */
    gle32(0x1000); /* align */

    gle32(2); /* PT_DYNAMIC */
    gphdr1(DYNAMIC_OFFSET, DYNAMIC_SIZE);
    gle32(6); /* PF_R | PF_W */
    gle32(0x4); /* align */

    /* now the interpreter name */
    glo = strcpy(glo, "/lib/ld-linux.so.2") + 0x14;

    /* now the dynamic section */
    gle32(1); /* DT_NEEDED */
    gle32(1); /* libc name */
    gle32(1); /* DT_NEEDED */
    gle32(11); /* libdl name */
    gle32(4); /* DT_HASH */
    gle32(hash + data_offset);
    gle32(6); /* DT_SYMTAB */
    gle32(dynsym + data_offset);
    gle32(5); /* DT_STRTAB */
    gle32(dynstr + data_offset);
    gle32(10); /* DT_STRSZ */
    gle32(dynstr_size);
    gle32(11); /* DT_SYMENT */
    gle32(16);
    gle32(17); /* DT_REL */
    gle32(rel + data_offset);
    gle32(18); /* DT_RELSZ */
    gle32(glo_saved - rel);
    gle32(19); /* DT_RELENT */
    gle32(8);
    gle32(0);  /* DT_NULL */
    gle32(0);

    t = fopen(c, "w");
    fwrite(data, 1, glo_saved - data, t);
    fclose(t);
}
#endif

/* Main function.
** `n`: argc.
** `t`: argv.
** Implicit argument type `int`. */
main(n, t)
{
    /* If command line arguments count is < 2. */
    if (n < 3) {
        /* Print usage. */
        printf("usage: otccelf file.c outfile\n");

        return 0;
    }

    /* 7JFQJ
    /* Create symbol stack and set the inital value. */
    dstk = strcpy(sym_stk = calloc(1, ALLOC_SIZE),
                  " int if else while break return for define main ") + TOK_STR_SIZE;

    /* Create data segment buffer. */
    glo = data = calloc(1, ALLOC_SIZE);

    /* Create instruction buffer. */
    ind = prog = calloc(1, ALLOC_SIZE);

    /* Create variables table. */
    vars = calloc(1, ALLOC_SIZE);

    /* Point `t` to the first argument, i.e. source file path.
    /* `t` was pointing to the program path.
    /* A pointer is 4 bytes in 32-bit program. */
    t = t + 4;

    /* Open source file. */
    file = fopen(*(int *)t, "r");

    /* Compute data segment offset taking ELF into account. */
    data_offset = ELF_BASE - data;

    /* Compute data segment buffer pointer taking ELF into account. */
    glo = glo + ELFSTART_SIZE;

    /* Compute instruction buffer pointer taking ELF into account. */
    ind = ind + STARTUP_SIZE;

    /* Read character. */
    inp();

    /* Read token. */
    next();

    /* Parse declaration. */
    decl(0);

    /* Point `t` to the second argument, i.e. output file path.
    /* `t` was pointing to the first argument.
    /* A pointer is 4 bytes in 32-bit program. */
    t = t + 4;

    #ifdef ELFOUT

    /* Create ELF binary file. */
    elf_out(*(int *)t);

    #else

    /* Create raw binary file. */

    /* Open output file. */
    file = fopen(*(int *)t, "w");

    /* Write instruction buffer to output file. */
    fwrite(prog, 1, ind - prog, file);

    /* Write data segment buffer to output file. */
    fwrite(prog, 1, glo - data, file);

    /* Close output file. */
    fclose(file);

    #endif

    return 0;
}
