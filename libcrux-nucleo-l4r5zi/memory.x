MEMORY
{
    FLASH : ORIGIN = 0x08000000, LENGTH = 2048K /* BANK_1 */
    RAM   : ORIGIN = 0x20000000, LENGTH =  640K /* SRAM */
}


/* This is where the call stack will be allocated. */
/* The stack is of the full descending type. */
/* We use this variable to locate the call stack and static variables
   in different memory regions.  For the L4R5ZI, we want to locate it
   at the top of SRAM3, the largest RAM region.  For more details, see
   https://md.cryspen.com/68n4HBCpR1qRe17_CRxiaQ */
/* _stack_start = 0x200a0000; */
/* _stack_end = 0x20000000; */
