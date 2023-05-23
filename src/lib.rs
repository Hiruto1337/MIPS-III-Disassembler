use num_derive::FromPrimitive;
use num_traits::FromPrimitive;

#[derive(Debug, FromPrimitive)]
pub enum Opcode {
    SPECIAL, REGIMM, J, JAL, BEQ, BNE, BLEZ, BGTZ,
    ADDI, ADDIU, SLTI, SLTIU, ANDI, ORI, XORI, LUI,
    COP0, COP1, COP2, BEQL = 20, BNEL, BLEZL, BGTZL,
    DADDI, DADDIU, LDL, LDR,
    LB = 32, LH, LWL, LW, LBU, LHU, LWR, LWU,
    SB, SH, SWL, SW, SDL, SDR, SWR, CACHE,
    LL, LWC1, LWC2, LLD = 52, LDC1, LDC2, LD,
    SC, SWC1, SWC2, SCD = 60, SDC1, SDC2, SD,
}

impl From<u32> for Opcode {
    fn from(inst: u32) -> Opcode {
        Opcode::from_u8((inst >> 26) as u8).unwrap()
    }
}

impl std::fmt::Display for Opcode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

pub enum Format {
    R(Opcode),
    I(Opcode),
    J(Opcode),
}

impl From<Opcode> for Format {
    fn from(opcode: Opcode) -> Self {
        use Opcode::*;
        match opcode {
            SPECIAL|COP0|COP1|COP2 => Format::R(opcode),
            ADDI|ADDIU|ANDI|DADDI|DADDIU|ORI|SLTI|SLTIU|
            XORI|REGIMM|BEQ|BEQL|BNE|BNEL|BLEZ|BLEZL|
            BGTZ|BGTZL|LUI|LDL|LDR|LB|LBU|LH|
            LHU|LWL|LW|LWR|LWU|SB|SH|SWL|
            SW|SDL|SDR|SWR|CACHE|LL|LWC1|LWC2|
            LLD|LDC1|LDC2|LD|SD|SC|SWC1|SWC2|
            SCD|SDC1|SDC2 => Format::I(opcode),
            J|JAL => Format::J(opcode)
        }
    }
}

#[derive(Debug, FromPrimitive)]
enum Funct {
    SLL, SRL = 2, SRA, SLLV, SRLV = 6, SRAV,
    JR, JALR, SYSCALL = 12, BREAK, SYNC = 15,
    MFHI, MTHI, MFLO, MTLO, DSLLV, DSRLV = 22, DSRAV,
    MULT, MULTU, DIV, DIVU, DMULT, DMULTU, DDIV, DDIVU,
    ADD, ADDU, SUB, SUBU, AND, OR, XOR, NOR,
    SLT = 42, SLTU, DADD, DADDU, DSUB, DSUBU,
    TGE, TGEU, TLT, TLTU, TEQ, TNE = 54,
    DSLL = 56,
    DSRL = 58,
    DSRA,
    DSLL32,
    DSRL32 = 62,
    DSRA32,
}

impl From<u8> for Funct {
    fn from(val: u8) -> Self {
        Funct::from_u8(val).unwrap()
    }
}

impl std::fmt::Display for Funct {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

#[derive(Debug, FromPrimitive)]
enum RegimmRt {
    BLTZ, BGEZ, BLTZL, BGEZL,
    TGEI = 8, TGEIU, TLTI, TLTIU, TEQI, TNEI = 14,
    BLTZAL = 16, BGEZAL, BLTZALL, BGEZALL
}

impl From<u8> for RegimmRt {
    fn from(val: u8) -> Self {
        RegimmRt::from_u8(val).unwrap()
    }
}

impl std::fmt::Display for RegimmRt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

#[derive(Debug, FromPrimitive)]
enum CopRs {
    MF, DMF, CF, MT = 4, DMT, CT,
    BC = 8,
    // Following are COP1 format fields
    S = 16, // Single (32 bits) binary floating-point
    D, // Double (64 bits) binary floating-point
    W = 20, // 32 bits binary fixed-point
    L // 64 bits binary fixed-point
}

impl From<u8> for CopRs {
    fn from(reg: u8) -> Self {
        CopRs::from_u8(reg.min(16)).unwrap()
    }
}

impl std::fmt::Display for CopRs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

#[derive(Debug, FromPrimitive)]
enum CopRt {
    BCF, BCT, BCFL, BCTL
}

impl From<u8> for CopRt {
    fn from(reg: u8) -> Self {
        CopRt::from_u8(reg).unwrap()
    }
}

impl std::fmt::Display for CopRt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

#[derive(Debug, FromPrimitive)]
enum CP0 {
    TLBR = 1, TLBWI, TLBWR = 6,
    TLBP = 8,
    ERET = 24
}

impl From<u8> for CP0 {
    fn from(reg: u8) -> Self {
        CP0::from_u8(reg).unwrap()
    }
}

impl std::fmt::Display for CP0 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

#[derive(Debug, FromPrimitive)]
enum CP1 {
    ADD, SUB, MUL, DIV, SQRT, ABS, MOV, NEG,
    RoundL, TruncL, CeilL, FloorL, RoundW, TruncW, CeilW, FloorW,
    CvtS = 32, CvtD, CvtW = 36, CvtL,
    CF = 48, CUn, CEq, CUeq, COlt, CUlt, COle, CUle,
    CSf, CNgle, CSeq, CNgl, CLt, CNge, CLe, CNgt
}

impl From<u8> for CP1 {
    fn from(val: u8) -> Self {
        CP1::from_u8(val).unwrap()
    }
}

impl std::fmt::Display for CP1 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

#[derive(Debug, FromPrimitive, Clone, Copy)]
pub enum Register {
    Zero,
    At,
    V0, V1,
    A0, A1, A2, A3,
    T0, T1, T2, T3, T4, T5, T6, T7,
    S0, S1, S2, S3, S4, S5, S6, S7,
    T8, T9,
    K0, K1,
    GP, // Global pointer
    SP, // Stack pointer
    FP, // Frame pointer
    RA, // Return address (only changed by JAL and JALR instructions (and JR?))
}

impl From<u8> for Register {
    fn from(reg: u8) -> Register {
        Register::from_u8(reg).unwrap()
    }
}

impl std::fmt::Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

pub struct Instruction {
    pub assembly: Vec<String>
}

impl From<(u32, &mut [u32; 35], &mut Vec<u32>)> for Instruction {
    fn from((inst, registers, jal_stack): (u32, &mut [u32; 35], &mut Vec<u32>)) -> Self {
        if inst == 0 {
            return Instruction {
                assembly: vec!["NOP".to_string()]
            }
        }
        
        let structure = Format::from(Opcode::from(inst));

        let assembly;
        use Format::*;

        match structure {
            R(opcode) => {
                let rs = ((inst >> 21) & ((1 << 5) - 1)) as u8;
                let rt = ((inst >> 16) & ((1 << 5) - 1)) as u8;
                let rd = ((inst >> 11) & ((1 << 5) - 1)) as u8;
                let sa = ((inst >> 6) & ((1 << 5) - 1)) as u8;
                let funct = (inst & ((1 << 6) - 1)) as u8;

                match opcode {
                    Opcode::SPECIAL => {
                        let rs = Register::from(rs);
                        let rt = Register::from(rt);
                        let rd = Register::from(rd);
                        let funct = Funct::from(funct);
                        use Funct::*;

                        match funct {
                            SLL|SRL|SRA|DSLL|DSRL|DSRA|DSLL32|DSRL32|DSRA32 => {
                                assembly = vec![funct.to_string(), rd.to_string(), rt.to_string(), sa.to_string()];
                            },
                            SLLV|SRLV|SRAV|DSLLV|DSRLV|DSRAV => {
                                assembly = vec![funct.to_string(), rd.to_string(), rt.to_string(), rs.to_string()];
                            },
                            JR|JALR|MTHI|MTLO => {
                                // JALR has two formats?
                                assembly = vec![funct.to_string(), rs.to_string()];
                            },
                            SYSCALL|BREAK|SYNC => {
                                assembly = vec![funct.to_string()];
                            },
                            MFHI|MFLO => {
                                assembly = vec![funct.to_string(), rd.to_string()];
                            },
                            MULT|MULTU|DIV|DIVU|DMULT|DMULTU|DDIV|DDIVU|TGE|TGEU|TLT|TLTU|TEQ|TNE => {
                                assembly = vec![funct.to_string(), rs.to_string(), rt.to_string()];
                            },
                            ADD|ADDU|SUB|SUBU|AND|OR|XOR|NOR|SLT|SLTU|DADD|DADDU|DSUB|DSUBU => {
                                assembly = vec![funct.to_string(), rd.to_string(), rs.to_string(), rt.to_string()];
                            }
                        }
                    },
                    _ => {
                        // Opcode is a COP-function
                        match rs {
                            val if val < 16 => {
                                let sub = CopRs::from(rs);
                                use CopRs::*;
                                match sub {
                                    MT | MF | CT | CF | DMT | DMF => {
                                        // Movement of either words or control
                                        let rt = Register::from(rt);
                                        let rd = Register::from(rd);
        
                                        assembly = vec![opcode.to_string(), sub.to_string(), rt.to_string(), rd.to_string()];
                                    },
                                    BC => {
                                        // Branch
                                        let br = CopRt::from(rt);
                                        let offset = (inst & ((1 << 16) - 1)) as u32;
        
                                        assembly = vec![opcode.to_string(), br.to_string(), offset.to_string()];
                                    },
                                    S | D | W | L => {
                                        // Floating point convertion
                                        let fmt = CopRs::from(rs);
                                        let fs = Register::from(rd);
                                        let fd = Register::from(sa);
                                        let funct = CP1::from(funct);
        
                                        assembly = vec![funct.to_string(), fmt.to_string(), fd.to_string(), fs.to_string()];
                                    }
                                }
                            },
                            _ => {
                                // It is a COP operation
                                match opcode {
                                    Opcode::COP0 => {
                                        let funct = CP0::from(funct);
                                        assembly = vec![funct.to_string()];
                                    },
                                    Opcode::COP1 => {
                                        let funct = CP1::from(funct);
                                        assembly = vec![funct.to_string()];
                                    }
                                    _ => {
                                        assembly = vec!["COP2".to_string()];
                                    }
                                }
                            }
                        }
                    }
                }
            },
            I(opcode) => {
                let rs = ((inst >> 21) & ((1 << 5) - 1)) as u8;
                let rt = ((inst >> 16) & ((1 << 5) - 1)) as u8;
                let imm_off = inst & ((1 << 16) - 1);
                use Opcode::*;
                match opcode {
                    LB|LBU|LH|LHU|LW|LWL|LWR|SB|
                    SH|SW|SWL|SWR|LD|LDL|LDR|LL|
                    LLD|LWU|SC|SCD|SD|SDL|SDR|LWC1|
                    SWC1|LDC1|SDC1|SWC2|LWC2 => {
                        let rt = Register::from(rt);
                        let base = Register::from(rs);

                        assembly = vec![opcode.to_string(), rt.to_string(), format!("{imm_off}({base})")];
                    },
                    ADDI|ADDIU|SLTI|SLTIU|ANDI|ORI|XORI|DADDI|DADDIU => {
                        let rt = Register::from(rt);
                        let rs = Register::from(rs);

                        match opcode {
                            ADDIU => {
                                registers[rt as usize] = registers[rs as usize] + imm_off as u32;
                            },
                            _ => {}
                        }
                        assembly = vec![opcode.to_string(), rt.to_string(), rs.to_string(), imm_off.to_string()]
                    },
                    LUI => {
                        let rt = Register::from(rt);
                        registers[rt as usize] = imm_off << 16;
                        assembly = vec![opcode.to_string(), rt.to_string(), imm_off.to_string()];
                    },
                    BEQ|BNE|BEQL|BNEL => {
                        let rs = Register::from(rs);
                        let rt = Register::from(rt);

                        assembly = vec![opcode.to_string(), rs.to_string(), rt.to_string(), imm_off.to_string()];
                    },
                    BLEZ|BGTZ|BLEZL|BGTZL => {
                        let rs = Register::from(rs);

                        assembly = vec![opcode.to_string(), rs.to_string(), imm_off.to_string()];
                    },
                    REGIMM => {
                        let rs = Register::from(rs);
                        let sub = RegimmRt::from(rt);
                        use RegimmRt::*;

                        match sub {
                            BLTZ|BGEZ|BLTZAL|BGEZAL|BLTZL|BGEZL|BLTZALL|BGEZALL|
                            TGEI|TGEIU|TLTI|TLTIU|TEQI|TNEI => {
                                let rs = Register::from(rs);

                                assembly = vec![sub.to_string(), rs.to_string(), imm_off.to_string()];
                            }
                        }
                    },
                    _ => {
                        assembly = vec![opcode.to_string(), format!("Unknown I-type instruction. Hex: {:x}", inst)];
                    }
                }
            },
            J(opcode) => {
                let opcode = opcode.to_string();
                let target = ((inst & ((1 << 26) - 1)) as u32).to_string();

                assembly = vec![opcode, target];
            }
        }

        Instruction {
            assembly
        }
    }
}

// Unit tests
#[cfg(test)]
mod tests {
    use crate::Instruction;

    #[test]
    fn test_opcodes() {
        let hex_codes = vec![
            0x012A4020, // ADD t0 t1 t2
            0x21280069, // ADDI t0 t1 0x69
        ];

        let instructions = vec![
            vec!["ADD", "T0", "T1", "T2", "0"],
            vec!["ADDI", "T0", "T1", "105"]
        ];

        for i in 0..hex_codes.len() {
            let inst = Instruction::from((hex_codes[i], &mut [0; 35], &mut vec![]));
            assert_eq!(inst.assembly, instructions[i]);
        }
    }
}