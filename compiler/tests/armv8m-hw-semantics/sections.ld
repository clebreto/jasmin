ENTRY(reset_handler)

SECTIONS
{
  .text :
  {
    KEEP(*(.vectors))
    *(.text .text.*)
    *(.rodata .rodata.*)
    . = ALIGN(4);
  } > FLASH

  _data_load = LOADADDR(.data);

  .data :
  {
    _data_start = .;
    *(.data .data.*)
    . = ALIGN(4);
    _data_end = .;
  } > RAM AT > FLASH

  .bss (NOLOAD) :
  {
    _bss_start = .;
    *(.bss .bss.* COMMON)
    . = ALIGN(4);
    _bss_end = .;
  } > RAM

  _stack_top = ORIGIN(RAM) + LENGTH(RAM);

  /DISCARD/ :
  {
    *(.note.GNU-stack)
    *(.ARM.exidx* .ARM.extab*)
    *(.comment)
  }
}
