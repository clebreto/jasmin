/* Arm MPS2+ AN505 (Cortex-M33), as emulated by QEMU (mps2-an505): the
   processor starts in Secure state, with its vector table at 0x10000000. */

MEMORY
{
  FLASH (rx)  : ORIGIN = 0x10000000, LENGTH = 4M
  RAM   (rwx) : ORIGIN = 0x38000000, LENGTH = 2M
}

INCLUDE sections.ld
