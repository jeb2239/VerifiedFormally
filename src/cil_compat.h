#ifndef __cil_compat__
#define __cil_compat__

// Get rid of some C language extensions that cil does not support.
#define availability(a, b)
#define __availability__(a, b, c)
#define _Nonnull
#define _Nullable


#define invar(c,i,...) __blockattribute__((invar((c),(i),__VA_ARGS__)))
#define post(c) __attribute__((post((c))))
#define pre(c)  __attribute__((pre((c))))
#define refine(c) __attribute__((refine(c)))

#endif // __cil_compat__
