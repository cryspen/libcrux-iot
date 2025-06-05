enum Instruction<'a> {
    Ld,
    Str,
    Mov,
    Bic,
    Orr,
    Eor,
    Ror,
    And,
    Add,
    Sub,
    Mvn,
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
        } else if line.contains("\teor") {
            Instruction::Eor
        } else if line.contains("\torr") {
            Instruction::Orr
        } else if line.contains("\tror") {
            Instruction::Ror
        } else if line.contains("\tand") {
            Instruction::And
        } else if line.contains("\tadd") {
            Instruction::Add
        } else if line.contains("\tsub") {
            Instruction::Sub
        } else if line.contains("\tmvn") {
            Instruction::Mvn
        } else if line.contains("\tlsl") {
            Instruction::Lsl
        } else {
            Instruction::Other(line)
        }
    }
}

struct CycleReport {
    pub loads: usize,
    pub stores: usize,
    pub moves: usize,
    pub bics: usize,
    pub ands: usize,
    pub orrs: usize,
    pub rors: usize,
    pub eors: usize,
    pub lsls: usize,
    pub adds: usize,
    pub subs: usize,
    pub mvns: usize,
    pub others: usize,
    pub ppln_ld: usize,
    pub ppln_str: usize,
}

fn count_cycles<'a>(instrs: impl Iterator<Item = Instruction<'a>>) -> CycleReport {
    let mut in_load_run = false;
    let mut loads: usize = 0;
    let mut stores: usize = 0;
    let mut moves: usize = 0;
    let mut bics: usize = 0;
    let mut ands: usize = 0;
    let mut orrs: usize = 0;
    let mut rors: usize = 0;
    let mut eors: usize = 0;
    let mut lsls: usize = 0;
    let mut adds: usize = 0;
    let mut subs: usize = 0;
    let mut mvns: usize = 0;
    let mut others: usize = 0;
    let mut ppln_ld: usize = 0;
    let mut ppln_str: usize = 0;

    for instr in instrs {
        match instr {
            Instruction::Ld => {
                // per-run penalty
                if !in_load_run {
                    ppln_ld += 1;
                    in_load_run = true;
                }

                loads += 1
            }
            Instruction::Str => {
                // store can be pipelined at the end of a load run
                if !in_load_run {
                    ppln_str += 1;
                }

                in_load_run = false;
                stores += 1;
            }
            Instruction::And => {
                ands += 1;
                in_load_run = false;
            }
            Instruction::Orr => {
                orrs += 1;
                in_load_run = false;
            }
            Instruction::Ror => {
                rors += 1;
                in_load_run = false;
            }
            Instruction::Mov => {
                moves += 1;
                in_load_run = false;
            }
            Instruction::Bic => {
                bics += 1;
                in_load_run = false;
            }
            Instruction::Lsl => {
                lsls += 1;
                in_load_run = false;
            }
            Instruction::Eor => {
                eors += 1;
                in_load_run = false;
            }
            Instruction::Add => {
                adds += 1;
                in_load_run = false;
            }
            Instruction::Sub => {
                subs += 1;
                in_load_run = false;
            }
            Instruction::Mvn => {
                mvns += 1;
                in_load_run = false;
            }
            Instruction::Other(inst) => {
                others += 1;
                eprintln!("found unrecognized instruction: {inst}");
                in_load_run = false;
            }
        }
    }

    CycleReport {
        loads,
        stores,
        moves,
        bics,
        ands,
        orrs,
        rors,
        eors,
        lsls,
        adds,
        subs,
        mvns,
        others,
        ppln_ld,
        ppln_str,
    }
}

fn main() {
    let lines: Vec<String> = std::io::stdin().lines().map(|res| res.unwrap()).collect();
    let CycleReport {
        loads,
        stores,
        moves,
        bics,
        ands,
        orrs,
        rors,
        eors,
        lsls,
        others,
        ppln_ld,
        ppln_str,
        adds,
        subs,
        mvns,
    } = count_cycles(lines.iter().map(String::as_str).map(Instruction::from_str));
    let normal = loads
        + stores
        + moves
        + bics
        + ands
        + orrs
        + rors
        + eors
        + lsls
        + adds
        + subs
        + mvns
        + others;
    let total = normal + ppln_str + ppln_ld;

    let fields = [
        ("loads         ", loads),
        ("stores        ", stores),
        ("moves         ", moves),
        ("bics          ", bics),
        ("ands          ", ands),
        ("orrs          ", orrs),
        ("rors          ", rors),
        ("eors          ", eors),
        ("lsls          ", lsls),
        ("others        ", others),
        ("subtotal      ", normal),
        ("pipeline (ld) ", ppln_ld),
        ("pipeline (str)", ppln_str),
        ("total         ", total),
    ];

    for (name, value) in fields {
        println!("{name} {value}")
    }
}
