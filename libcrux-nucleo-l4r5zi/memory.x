MEMORY
{
    FLASH : ORIGIN = 0x08000000, LENGTH = 2048K /* BANK_1 */
    RAM   : ORIGIN = 0x20000000, LENGTH =  640K /* SRAM */
}


/* This is where the call stack will be allocated. */
/* The stack is of the full descending type. */
/* You may want to use this variable to locate the call stack and static
   variables in different memory regions. Below is shown the default value */
_stack_start = 0x200a0000;
