use binary::{Instruction};

fn main() {
    let z64_file = "sm64.z64";
    let file = std::fs::read(format!("/Users/lassegrosbol-rais/Desktop/{z64_file}"));

    // Create registers
    // registers = [0..31 = GPR, 32 = PC, 33 = LO, 34 = HI]
    let mut registers = [0; 35];

    if let Ok(content) = file {
        // ROM Entry Point
        let rom_ep = 0x1000;
        // RAM Entry Point
        let ram_ep = ((content[8] as u32) << 24)
        | ((content[9] as u32) << 16)
        | ((content[10] as u32) << 8)
        | (content[11] as u32);

        registers[32] = ram_ep; // Set PC to RAM entry point
        let mut jal_stack: Vec<u32> = vec![0x80247DF8];
        loop {
            let rom_pc = registers[32] - ram_ep + rom_ep;
            let big_endian: u32 = ((content[rom_pc as usize] as u32) << 24)
                | ((content[rom_pc as usize + 1] as u32) << 16)
                | ((content[rom_pc as usize + 2] as u32) << 8)
                | (content[rom_pc as usize + 3] as u32);

            let instruction = Instruction::from((big_endian, &mut registers, &mut jal_stack)).assembly;

            println!("PC: {rom_pc} - {}", instruction.join(" "));

            // if instruction[0] == "JAL" {
            //     jal_stack.push(pc);
            //     let msbs = (pc >> 28) << 28;
            //     let target = instruction[1].parse::<u32>().unwrap() << 2;
            //     pc = msbs | target;
            // } else if instruction[0] == "JR" {
            //     pc = jal_stack.pop().unwrap();
            // }

            registers[32] += 4;
        }
    }
}
