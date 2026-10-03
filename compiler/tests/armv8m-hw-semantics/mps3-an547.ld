/* Arm MPS3 AN547 (Cortex-M55), as emulated by QEMU: 512 KB of ITCM at 0, used
   as the flash, 512 KB of DTCM at 0x20000000. */

MEMORY
{
  FLASH (rx)  : ORIGIN = 0x00000000, LENGTH = 512K
  RAM   (rwx) : ORIGIN = 0x20000000, LENGTH = 512K
}

INCLUDE sections.ld
