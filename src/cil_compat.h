#ifndef __cil_compat__
#define __cil_compat__

// Get rid of some C language extensions that cil does not support.
#define __attribute__(x)
#define _Nonnull
#define _Nullable

#endif // __cil_compat__
