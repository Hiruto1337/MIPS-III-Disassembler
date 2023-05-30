use binary::{COPRegister::*, COPRegisters, Instruction, Register::*, Registers, virtual_to_physical};

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

    let mut jal_stack: Vec<u32> = vec![];

    let mut memory = PhysicalMemory::new();

    if let Ok(content) = file {
        // Load 0x1000 bytes from ROM into SP DMEM
        memory.sp_dmem.copy_from_slice(&content[..0x1000]);

        // Load 1 MiB from ROM into RDRAM
        memory.rd_ram[0x400..0x100400].copy_from_slice(&content[0..0x100000]);

        // Boot ROM Entry Point
        let boot_rom_entry = 0x40;

        // Boot RAM Entry Point
        let boot_ram_entry = 0xA4000040;

        registers[PC] = boot_ram_entry;

        loop {
            let rom_pc = virtual_to_physical(registers[PC]);
            let mut instruction = Instruction::from((&mut registers, &mut memory, &content,));
            println!("PC: {rom_pc} - {:?}", instruction.assembly);
            instruction.execute();

            registers[PC] += 4;
        }

        // // ROM Entry Point
        // let rom_entry = 0x1000;

        // // RAM Entry Point
        // let ram_entry = big_endian(&content, 0x8);

        // registers[PC] = ram_entry; // Set PC to RAM entry point (shouldn't boot code set entry point?)
        // loop {
        //     let rom_pc = registers[PC] - ram_entry + rom_entry;

        //     let hex = big_endian(&content, rom_pc as usize);

        //     let instruction = Instruction::from((hex, &mut registers, &mut jal_stack)).assembly;

        //     println!("PC: {rom_pc} - {}", instruction.join(" "));

        //     registers[PC] += 4;
        // }
    }
}
