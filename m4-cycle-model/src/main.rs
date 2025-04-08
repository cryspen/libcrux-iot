enum Instruction<'a> {
    Ld,
    Str,
    Mov,
    Bic,
    Orr,
    Lsl,
    #[allow(dead_code)]
    Other(&'a str),
}

impl<'a> Instruction<'a> {
    fn from_str(line: &'a str) -> Instruction<'a> {
        if line.contains("\tldr") || line.contains("\tldm") {
            Instruction::Ld
        } else if line.contains("\tstr") {
            Instruction::Str
        } else if line.contains("\tmov") {
            Instruction::Mov
        } else if line.contains("\tbic") {
            Instruction::Bic
        } else if line.contains("\torr") {
            Instruction::Orr
        } else if line.contains("\torr") {
            Instruction::Lsl
        } else {
            Instruction::Other(line)
        }
    }
}

fn count_cycles<'a>(instrs: impl Iterator<Item = Instruction<'a>>) -> usize {
    let mut in_load_run = false;
    let mut cycles = 0;

    for instr in instrs {
        match instr {
            Instruction::Ld => {
                // per-run penalty
                if !in_load_run {
                    cycles += 1;
                    in_load_run = true;
                }

                cycles += 1
            }
            Instruction::Str => {
                // store can be pipelined at the end of a load run
                if !in_load_run {
                    cycles += 1;
                }

                in_load_run = false;
                cycles += 1;
            }
            _ => {
                cycles += 1;
                in_load_run = false;
            }
        }
    }

    cycles
}

fn main() {
    let lines: Vec<String> = std::io::stdin().lines().map(|res| res.unwrap()).collect();

    let cycles = count_cycles(lines.iter().map(String::as_str).map(Instruction::from_str));
    println!("{cycles}");
}
