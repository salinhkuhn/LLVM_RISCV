# RiscvDialect
This prpject contains a riscv dialect using the Lean-MLIR project framework. To guarantee semantics according to the RISC-V spec we proof that the semantics of each instruction in our RV64 EXACTLY modells a step in the untouched sail modell. 


To extend the dialect:
    add instructions 
    extract bit vecotr operations using the other sail project and proof the bit vecotr extraction
    use the bit vec extraction as the semantic definition
    peoof that execution one step in the idalect is exactly one step in the untoiuched sail modell. 

whenever changing something in the dialect think of according change it in 