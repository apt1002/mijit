Register allocation:

# Global

On x86:

 - SP - Stack pointer. Base address for spill slots?
 - R8 - Base address for "persistent" values: those that last longer than one
   call to `mijit_run()`.
 - R12 - Temporary register for use by lowerer. R12 is a good choice because
   the lowerer mostly doesn't use the temporary register as a base address, and
   using R12 as a base address requires an extra SIB byte.
 - RDI - Within Beetle, temporary register for use by Builder.
