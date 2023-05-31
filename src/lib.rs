use std::ops::{Index, IndexMut};

use num_derive::FromPrimitive;
use num_traits::FromPrimitive;

pub struct Registers {registers: [u32; 35]}

impl Registers {
    pub fn new() -> Self {
        Registers { registers: [0; 35] }
    }
}

impl Index<Register> for Registers {
    type Output = u32;
    fn index(&self, index: Register) -> &Self::Output {
        &self.registers[index as usize]
    }
}

impl IndexMut<Register> for Registers {
    fn index_mut(&mut self, index: Register) -> &mut Self::Output {
        &mut self.registers[index as usize]
    }
}

impl std::fmt::Display for Registers {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.registers)
    }
}

pub struct COPRegisters {registers: [u32; 32]}

impl COPRegisters {
    pub fn new() -> Self {
        COPRegisters { registers: [0; 32] }
    }
}

impl Index<COPRegister> for COPRegisters {
    type Output = u32;
    fn index(&self, index: COPRegister) -> &Self::Output {
        &self.registers[index as usize]
    }
}

impl IndexMut<COPRegister> for COPRegisters {
    fn index_mut(&mut self, index: COPRegister) -> &mut Self::Output {
        &mut self.registers[index as usize]
    }
}

pub enum COPRegister {
    Index, Random, EntryLo0, EntryLo1, Context, PageMask, Wired, BadVAddr = 8,
    Count, EntryHi, Compare, Status, Cause, EPC, PRId, Config,
    LLAddr, WatchLo, WatchHi, XContext, ParityErr = 26, CacheErr, TagLo, TagHi,
    ErrorEPC
}

#[derive(Debug, FromPrimitive, Default, Clone, Copy)]
pub enum Opcode {
    #[default]
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

#[derive(Debug, FromPrimitive, Clone, Copy)]
pub enum Funct {
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

#[derive(Debug, FromPrimitive, Clone, Copy)]
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

#[derive(Debug, FromPrimitive, Clone, Copy)]
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

#[derive(Debug, FromPrimitive, Clone)]
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
    PC, // Program counter
    LO,
    HI
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

#[derive(Default)]
pub struct Instruction<'a> {
    pub assembly: Vec<String>,
    memory: Option<&'a mut PhysicalMemory>,
    registers: Option<&'a mut Registers>,
    opcode: Option<Opcode>,
    funct: Option<Funct>,
    rs: Option<Register>,
    rt: Option<Register>,
    rd: Option<Register>,
    sa: Option<u8>,
    immediate: Option<i16>,
    target: Option<u32>,
    sub: Option<CopRs>,
    br: Option<CopRt>,
    fmt: Option<CopRs>,
    fs: Option<Register>,
    fd: Option<Register>,
    cop0_funct: Option<CP0>,
    cop1_funct: Option<CP1>
}

impl<'a> From<(&'a mut Registers, &'a mut PhysicalMemory)> for Instruction<'a> {
    fn from((registers, memory): (&'a mut Registers, &'a mut PhysicalMemory)) -> Self {
        let phys_addr = virtual_to_physical(registers[Register::PC]);
        let (mem_block, offset) = memory.from_physical_address(phys_addr);
        let inst = big_endian(&mem_block, offset as usize);

        let mut instruction = Instruction::default();
        instruction.registers = Some(registers);

        if inst == 0 {
            instruction.assembly = vec![format!("NOP")];
            return instruction;
        }
        
        let structure = Format::from(Opcode::from(inst));
        let assembly = &mut instruction.assembly;

        match structure {
            Format::R(opcode) => {
                // Standard parameters
                let rs = Register::from(((inst >> 21) & ((1 << 5) - 1)) as u8);
                let rt = Register::from(((inst >> 16) & ((1 << 5) - 1)) as u8);
                let rd = Register::from(((inst >> 11) & ((1 << 5) - 1)) as u8);
                let sa = ((inst >> 6) & ((1 << 5) - 1)) as u8;
                let funct = Funct::from((inst & ((1 << 6) - 1)) as u8);
                let offset = (inst << 16) >> 16 as u32;

                // Set instruction parameters
                instruction.opcode = Some(opcode);
                instruction.rs = Some(rs);
                instruction.rt = Some(rt);
                instruction.rd = Some(rd);
                instruction.sa = Some(sa);
                instruction.funct = Some(funct);

                match opcode {
                    Opcode::SPECIAL => {
                        use Funct::*;
                        match funct {
                            SLL|SRL|SRA|DSLL|DSRL|DSRA|DSLL32|DSRL32|DSRA32 => *assembly = vec![funct.to_string(), rd.to_string(), rt.to_string(), sa.to_string()],

                            SLLV|SRLV|SRAV|DSLLV|DSRLV|DSRAV => *assembly = vec![funct.to_string(), rd.to_string(), rt.to_string(), rs.to_string()],

                            JR|JALR|MTHI|MTLO => *assembly = vec![funct.to_string(), rs.to_string()],

                            SYSCALL|BREAK|SYNC => *assembly = vec![funct.to_string()],

                            MFHI|MFLO => *assembly = vec![funct.to_string(), rd.to_string()],

                            MULT|MULTU|DIV|DIVU|DMULT|DMULTU|DDIV|DDIVU|TGE|TGEU|TLT|TLTU|TEQ|TNE => *assembly = vec![funct.to_string(), rs.to_string(), rt.to_string()],

                            ADD|ADDU|SUB|SUBU|AND|OR|XOR|NOR|SLT|SLTU|DADD|DADDU|DSUB|DSUBU => *assembly = vec![funct.to_string(), rd.to_string(), rs.to_string(), rt.to_string()],
                        }
                    },
                    _ => {
                        // Opcode is a COP-function
                        match rs as u8 {
                            val if val < 16 => {
                                let sub = CopRs::from(rs as u8);
                                instruction.sub = Some(sub);
                                use CopRs::*;
                                match sub {
                                    MT | MF | CT | CF | DMT | DMF => {
                                        // Movement of either words or control
                                        *assembly = vec![sub.to_string(), opcode.to_string(), rt.to_string(), rd.to_string()];
                                    },
                                    BC => {
                                        // Branch
                                        let br = CopRt::from(rt as u8);
                                        instruction.br = Some(br);
                                        use CopRt::*;
                                        match br {
                                            BCT => *assembly = vec![format!("B"), opcode.to_string(), format!("T"), offset.to_string()],
                                            BCF => *assembly = vec![format!("B"), opcode.to_string(), format!("F"), offset.to_string()],
                                            BCTL => *assembly = vec![format!("B"), opcode.to_string(), format!("TL"), offset.to_string()],
                                            BCFL => *assembly = vec![format!("B"), opcode.to_string(), format!("FL"), offset.to_string()]
                                        }
                                    },
                                    S | D | W | L => {
                                        // Floating point convertion
                                        let fmt = CopRs::from(rs as u8);
                                        let fs = Register::from(rd);
                                        let fd = Register::from(sa);
                                        let cop1_funct = CP1::from(funct as u8);

                                        instruction.fmt = Some(fmt);
                                        instruction.fs = Some(fs);
                                        instruction.fd = Some(fd);
                                        instruction.cop1_funct = Some(cop1_funct.to_owned());
                                        *assembly = vec![cop1_funct.to_string(), fmt.to_string(), fd.to_string(), fs.to_string()];
                                    }
                                }
                            },
                            _ => match opcode {
                                // It is a COP operation
                                Opcode::COP0 => {
                                    let cop0_funct = CP0::from(funct as u8);
                                    instruction.cop0_funct = Some(cop0_funct);
                                    *assembly = vec![funct.to_string()];
                                },
                                Opcode::COP1 => {
                                    let cop1_funct = CP1::from(funct as u8);
                                    instruction.cop1_funct = Some(cop1_funct);
                                    *assembly = vec![funct.to_string()];
                                }
                                _ => {
                                    // TO-DO: SERIOUSLY NEEDS SPECIFICITY
                                    *assembly = vec!["COP2".to_string()];
                                }
                            }
                        }
                    }
                }
            },
            Format::I(opcode) => {
                let rs = Register::from(((inst >> 21) & ((1 << 5) - 1)) as u8);
                let rt = Register::from(((inst >> 16) & ((1 << 5) - 1)) as u8);
                let sub = RegimmRt::from(rt as u8);
                let immediate = (inst & ((1 << 16) - 1)) as i16;
                use Opcode::*;
                match opcode {
                    LB|LBU|LH|LHU|LW|LWL|LWR|SB|
                    SH|SW|SWL|SWR|LD|LDL|LDR|LL|
                    LLD|LWU|SC|SCD|SD|SDL|SDR|LWC1|
                    SWC1|LDC1|SDC1|SWC2|LWC2 => *assembly = vec![opcode.to_string(), rt.to_string(), format!("{immediate}({rs})")],

                    ADDI|ADDIU|SLTI|SLTIU|ANDI|ORI|XORI|DADDI|DADDIU => *assembly = vec![opcode.to_string(), rt.to_string(), rs.to_string(), immediate.to_string()],

                    LUI => *assembly = vec![opcode.to_string(), rt.to_string(), format!("0x{:x}", immediate)],

                    BEQ|BNE|BEQL|BNEL => *assembly = vec![opcode.to_string(), rs.to_string(), rt.to_string(), immediate.to_string()],

                    BLEZ|BGTZ|BLEZL|BGTZL => *assembly = vec![opcode.to_string(), rs.to_string(), immediate.to_string()],

                    REGIMM => {
                        *assembly = vec![sub.to_string(), rs.to_string(), immediate.to_string()];

                        // use RegimmRt::*;
                        // match sub {
                        //     BLTZ|BGEZ|BLTZAL|BGEZAL|BLTZL|BGEZL|BLTZALL|BGEZALL|
                        //     TGEI|TGEIU|TLTI|TLTIU|TEQI|TNEI => {
                        //         let rs = Register::from(rs);
                        //     }
                        // }
                    },
                    _ => *assembly = vec![opcode.to_string(), format!("Unknown I-type instruction. Hex: {:x}", inst)]
                }
            },
            Format::J(opcode) => {
                let target = (inst << 6) >> 4;
                *assembly = vec![opcode.to_string(), target.to_string()];
                instruction.target = Some(target);
            }
        }

        instruction
    }
}

impl<'a> std::fmt::Display for Instruction<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.assembly.join(" "))
    }
}

impl<'a> Instruction<'a> {
    pub fn execute(&mut self) {
        if let None = self.opcode {
            return;
        }

        let opcode = self.opcode.unwrap();
        
        let inst_type = Format::from(opcode);
        let registers = self.registers.take().unwrap();
        let memory = self.memory.take().unwrap();

        use Opcode::*;
        match inst_type {
            Format::R(opcode) => {
                let rs = self.rs.unwrap();
                let rt = self.rt.unwrap();
                let rd = self.rd.unwrap();
                let sa = self.sa.unwrap();
                let funct = self.funct.unwrap();
                use Funct::*;

                match opcode {
                    SPECIAL => {
                        match funct {
                            SLL => registers[rd] = registers[rt] << sa,
                            SRL => registers[rd] = registers[rt] >> sa,
                            JR => registers[Register::PC] = memory.jal_stack.pop().unwrap(),
                            OR => registers[rd] = registers[rs] | registers[rt],
                            _ => {}
                        }
                    },
                    _ => {
                        // COP
                        match rs as u8 {
                            val if val < 16 => {
                                let sub = self.sub.unwrap();
                                use CopRs::*;
                                match sub {
                                    MT => {},
                                    MF => {},
                                    CT => {},
                                    CF => {},
                                    DMT => {},
                                    DMF => {}
                                    BC => {
                                        let br = self.br.unwrap();
                                        use CopRt::*;
                                        match br {
                                            BCT => {},
                                            BCF => {},
                                            BCTL => {},
                                            BCFL => {}
                                        }
                                    },
                                    S => {},
                                    D => {},
                                    W => {},
                                    L => {}
                                }
                            },
                            _ => {
                                use CP0::*;
                                use CP1::*;
                                match opcode {
                                    Opcode::COP0 => match self.cop0_funct.take().unwrap() {
                                        TLBR => {},
                                        TLBP => {},
                                        TLBWI => {},
                                        TLBWR => {},
                                        ERET => {}
                                    },
                                    Opcode::COP1 => match self.cop1_funct.take().unwrap() {
                                        ADD => {},
                                        SUB => {},
                                        MUL => {},
                                        DIV => {},
                                        SQRT => {},
                                        ABS => {},
                                        MOV => {},
                                        NEG => {},
                                        RoundL => {},
                                        TruncL => {},
                                        CeilL => {},
                                        FloorL => {},
                                        RoundW => {},
                                        TruncW => {},
                                        CeilW => {},
                                        FloorW => {},
                                        CvtS => {},
                                        CvtD => {},
                                        CvtW => {},
                                        CvtL => {},
                                        CF => {},
                                        CUn => {},
                                        CEq => {},
                                        CUeq => {},
                                        COlt => {},
                                        CUlt => {},
                                        COle => {},
                                        CUle => {},
                                        CSf => {},
                                        CNgle => {},
                                        CSeq => {},
                                        CNgl => {},
                                        CLt => {},
                                        CNge => {},
                                        CLe => {},
                                        CNgt => {}
                                    }
                                    _ => {
                                        // TO-DO: SERIOUSLY NEEDS SPECIFICITY
                                    }
                                }
                            }
                        }
                    }
                }
            },
            Format::J(_) => {
                let target = self.target.unwrap();
                let new_pc = (((registers[Register::PC] + 4) >> 28) << 28) | target;

                use Opcode::*;
                use Register::*;
                match opcode {
                    JAL => {
                        // Instruction AFTER JAL is also to be executed before jump
                        memory.jal_stack.push(registers[PC]);
                        registers[RA] = registers[PC];
                        registers[PC] = new_pc;
                    },
                    _ => {
                        registers[PC] = new_pc;
                    }
                }
            },
            Format::I(_) => {
                let rs = self.rs.unwrap();
                let rt = self.rt.unwrap();
                let immediate = self.immediate.unwrap();

                match opcode {
                    ADDI => match immediate as i32 {
                        val if val < 0 => match registers[rs].checked_sub(val.abs() as u32) {
                            Some(result) => registers[rt] = result,
                            None => println!("Execute exception... (Subtract overflow)")
                        },
                        val => match registers[rs].checked_add(val as u32) {
                            Some(result) => registers[rt] = result,
                            None => println!("Execute exception... (Add with overflow)")
                        }
                    }
                    ADDIU => match immediate as i32 {
                        val if val < 0 => registers[rt] = registers[rs].overflowing_sub(val.abs() as u32).0,
                        val => registers[rt] = registers[rs].overflowing_add(val as u32).0
                    }
                    ANDI => registers[rt] = registers[rs] & (((immediate as u32) << 16) >> 16),
                    ORI => registers[rt] = registers[rs] | immediate as u32,
                    SLTI => registers[rt] = ((registers[rs] as i32) < (immediate as i32)) as u32,
                    XORI => registers[rt] = registers[rs] ^ (((immediate as u32) << 16) >> 16),
                    LUI => registers[rt] = (immediate as u32) << 16,
                    BNE => if registers[rs] != registers[rt] {
                        match (immediate as i32) << 2 {
                            val if val < 0 => registers[Register::PC] -= val.abs() as u32,
                            val => registers[Register::PC] += val as u32
                        }
                    },
                    BEQL => if registers[rs] == registers[rt] {
                        // Execute delay instruction
                        registers[Register::PC] += 4;
                        let mut delay_instruction = Instruction::from((registers, memory));
                        delay_instruction.execute();

                        let registers = delay_instruction.return_mut_registers();

                        // Update PC
                        registers[Register::PC] -= 4;
                        match (immediate as i32) << 2 {
                            val if val < 0 => registers[Register::PC] -= val.abs() as u32,
                            val => registers[Register::PC] += val as u32
                        }
                    } else {
                        // Skip delay instruction
                        registers[Register::PC] += 4;
                    }
                    _ => {}
                }
            }
        }
    }

    fn return_mut_registers(&mut self) -> &mut Registers {
        self.registers.take().unwrap()
    }
}

// Convert four bytes into a single word
pub fn big_endian(content: &Vec<u8>, offset: usize) -> u32 {
    ((content[offset as usize] as u32) << 24)
        | ((content[offset as usize + 1] as u32) << 16)
        | ((content[offset as usize + 2] as u32) << 8)
        | (content[offset as usize + 3] as u32)
}

// Convert a virtual address into a physical address
pub fn virtual_to_physical(virtual_address: u32) -> u32 {
    match virtual_address {
        addr if addr < 0x80000000 => addr, // KUSEG
        addr if addr < 0xA0000000 => addr - 0x80000000, // KSEG0
        addr if addr < 0xC0000000 => addr - 0xA0000000, // KSEG1
        addr if addr < 0xE0000000 => addr, // KSSEG
        addr => addr // KSEG3
    }
}

pub struct PhysicalMemory {
    pub rd_ram: Vec<u8>, // 0x0 - 0x3FFFFF
    pub sp_dmem: Vec<u8>, // 0x4000000 - 0x4000FFF
    pub sp_imem: Vec<u8>, // 0x4001000 - 0x4001FFF
    pub jal_stack: Vec<u32>
}

impl PhysicalMemory {
    pub fn new() -> Self {
        PhysicalMemory {
            rd_ram: vec![0; 0x3FFFFF],
            sp_dmem: vec![0; 0x1000],
            sp_imem: vec![0; 0x1000],
            jal_stack: vec![]
        }
    }

    pub fn from_physical_address(&mut self, physical_address: u32) -> (&mut Vec<u8>, u32) {
        match physical_address {
            addr if addr < 0x400000 => (&mut self.rd_ram, physical_address),
            addr if addr < 0x401000 => (&mut self.sp_dmem, physical_address - 0x400000),
            addr if addr < 0x402000 => (&mut self.sp_imem, physical_address - 0x401000),
            _ => (&mut self.rd_ram, physical_address)
        }
    }
}