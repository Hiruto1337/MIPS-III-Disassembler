use binary::{COPRegister::*, COPRegisters, Instruction, Register::*, Registers, virtual_to_physical, PhysicalMemory};

fn main() {
    let z64_file = "sm64.z64";
    let file = std::fs::read(format!("/Users/lassegrosbol-rais/Desktop/{z64_file}"));

    // Create registers and boot N64 (initialize registers) (https://n64.readthedocs.io/#boot-process)
    println!("Booting Nintendo 64...");

    let mut registers = Registers::new();
    registers[T3] = 0xA4000040;
    registers[S4] = 0x1;
    registers[S6] = 0x3F;
    registers[SP] = 0xA4001FF0;

    let mut cop_registers = COPRegisters::new();
    cop_registers[Random] = 0x1F;
    cop_registers[Status] = 0x34000000;
    cop_registers[PRId] = 0xB00;
    cop_registers[Config] = 0x6E463;

    let mut memory = PhysicalMemory::new();

    if let Ok(content) = file {
        // Load 0x1000 bytes from ROM into SP DMEM
        memory.sp_dmem = content[..0x1000].to_owned();

        // Load 1 MiB from ROM into RDRAM
        memory.rd_ram[0x400..0x100400].copy_from_slice(&content[0..0x100000]);

        // Set PC to RAM Entry
        registers[PC] = 0xA4000040; // What is the real entry point?

        loop {
            let mut instruction = Instruction::from((&mut registers, &mut memory));
            println!("{:?}", instruction.assembly);
            instruction.execute();

            registers[PC] += 4;
        }
    }
}
