use clap::Parser;

use std::io::Write;

use std::time::Duration;

#[derive(Parser, Debug)]
struct Args {
    #[arg(short, long)]
    device: String,
}

fn main() {
    let args = Args::parse();

    let mut port = serialport::new(&args.device, 115_200)
        .timeout(Duration::from_millis(10))
        .open()
        .expect("Failed to open port");

    port.write(b"output").expect("write failed");
}
