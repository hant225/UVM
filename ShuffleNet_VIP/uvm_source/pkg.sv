`timescale 1ns / 1ps

package my_pkg;
    localparam pDATA_WIDTH        = 8;
    localparam pINPUT_WIDTH       = 224;
    localparam pINPUT_HEIGHT      = 224;
    localparam pWEIGHT_DATA_WIDTH = 64;
    localparam pWEIGHT_BASE_ADDR  = 32'h4000_0000;
    localparam pIN_CHANNEL        = 3;
    localparam pOUT_CHANNEL       = 24;
    localparam pKERNEL_SIZE       = 3;    
    localparam pACTIVATION        = "relu";
    localparam pOUTPUT_PARALLEL   = 24;
    localparam pPADDING           = 1;
    localparam pSTRIDE            = 2;    
    
    localparam pOUTPUT_WIDTH      = (pINPUT_WIDTH - pKERNEL_SIZE + 2*pPADDING)/pSTRIDE + 1;
    localparam pOUTPUT_HEIGHT     = (pINPUT_HEIGHT - pKERNEL_SIZE + 2*pPADDING)/pSTRIDE + 1;        
    localparam pBLOCK_RAM_NUM     = pOUTPUT_PARALLEL/2;
    localparam pULTRA_RAM_NUM     = (pIN_CHANNEL*pOUTPUT_PARALLEL)/8;
    localparam pKERNEL_NUM        = pIN_CHANNEL*pOUT_CHANNEL*pKERNEL_SIZE*pKERNEL_SIZE / (pWEIGHT_DATA_WIDTH/pDATA_WIDTH);
    localparam pBIAS_NUM          = pOUT_CHANNEL / 2;
    localparam pDEQUANT_SCALE_NUM = pOUT_CHANNEL;
    localparam pWEIGHTS_NUM       = pKERNEL_NUM + pBIAS_NUM + pDEQUANT_SCALE_NUM + 1;
    
    int global_fd = 0;    
endpackage


