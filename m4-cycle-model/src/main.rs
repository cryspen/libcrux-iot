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

struct CycleReport {
    pub normal: usize,
    pub ppln_ld: usize,
    pub ppln_str: usize,
}

fn count_cycles<'a>(instrs: impl Iterator<Item = Instruction<'a>>) -> CycleReport {
    let mut in_load_run = false;
    let mut cycles = CycleReport {
        normal: 0,
        ppln_ld: 0,
        ppln_str: 0,
    };

    for instr in instrs {
        match instr {
            Instruction::Ld => {
                // per-run penalty
                if !in_load_run {
                    cycles.ppln_ld += 1;
                    in_load_run = true;
                }

                cycles.normal += 1
            }
            Instruction::Str => {
                // store can be pipelined at the end of a load run
                if !in_load_run {
                    cycles.ppln_str += 1;
                }

                in_load_run = false;
                cycles.normal += 1;
            }
            _ => {
                cycles.normal += 1;
                in_load_run = false;
            }
        }
    }

    cycles
}

fn main() {
    let lines: Vec<String> = std::io::stdin().lines().map(|res| res.unwrap()).collect();
    let CycleReport {
        normal,
        ppln_ld,
        ppln_str,
    } = count_cycles(lines.iter().map(String::as_str).map(Instruction::from_str));
    let total = normal + ppln_str + ppln_ld;

    println!("normal    pipeline (ld)     pipeline (str)      total");
    println!(
        "{: >6}    {: >13}     {: >14}    {: >7}",
        normal, ppln_ld, ppln_str, total,
    );
}
