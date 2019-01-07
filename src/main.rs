use nice_tree;

use std::io;
use std::io::prelude::*;

fn print_command_line_syntax()
{
    println!("Parameters:");
    println!("  -h - Prints this command line syntax.");
    println!("  -o <FilePath> - Path to output file. If not specified, output is written to standard output.");
    println!("  -i <FilePath> - Path to input file. If not specified, input is read from standard input.");
    println!("  -d <Data> - Input content specified directly as a parameter.");
    println!("  -g <FullPercent> <MaxLevels> - Generate random tree.");
}

enum Input {
    None,
    Some(String),
    Random { full_percent: u32, max_levels: u32 },
}

enum Output {
    StdOut,
    File(String),
}

#[derive(Debug, Clone)]
struct MyError
{
    message: String,
}
impl MyError {
    fn missing_parameter() -> Self {
        MyError { message: String::from("Missing parameter.") }
    }
}
impl std::error::Error for MyError {
    fn description(&self) -> &str { &self.message }
    fn cause(&self) -> Option<&std::error::Error> { None }
}
impl std::fmt::Display for MyError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", &self.message)
    }
}
impl std::convert::From<std::io::Error> for MyError {
    fn from(error: std::io::Error) -> Self {
        MyError{ message: format!("{:?}", error) }
    }
}
impl std::convert::From<std::num::ParseIntError> for MyError {
    fn from(error: std::num::ParseIntError) -> Self {
        MyError{ message: format!("{:?}", error) }
    }
}
impl std::convert::From<nice_tree::parser::ParseError> for MyError {
    fn from(error: nice_tree::parser::ParseError) -> Self {
        MyError{ message: format!("{:?}", error) }
    }
}
impl std::convert::From<&str> for MyError {
    fn from(message: &str) -> Self {
        MyError{ message: String::from(message) }
    }
}

fn main() -> Result<(), MyError> {
    let mut args_iter = std::env::args();

    // Skip executable name.
    args_iter.next().unwrap();

    let mut input = Input::None;
    let mut output = Output::StdOut;

    while let Some(arg) = args_iter.next() {
        match arg.as_ref() {
            "-h" => {
                print_command_line_syntax();
                return Ok(());
            }
            "-o" => {
                let file_path = args_iter.next().ok_or_else(
                    ||{ MyError::missing_parameter() })?;
                output = Output::File(file_path);
            }
            "-i" => {
                let file_path = args_iter.next().ok_or_else(
                    ||{ MyError::missing_parameter() })?;
                input = Input::Some(std::fs::read_to_string(file_path)?);
            }
            "-d" => {
                let data = args_iter.next().ok_or_else(
                    ||{ MyError::missing_parameter() })?;
                input = Input::Some(data);
            }
            "-g" => {
                let full_percent = args_iter.next().ok_or_else(
                    ||{ MyError::missing_parameter() })?.parse::<u32>()?;
                let max_levels = args_iter.next().ok_or_else(
                    ||{ MyError::missing_parameter() })?.parse::<u32>()?;
                input = Input::Random{ full_percent, max_levels };
            }
            _ => {
                return Err(MyError::from("Unknown parameter."));
            }
        }
    }

    // Read input from stdin.
    if let Input::None = input {
        let mut s = String::new();
        io::stdin().read_to_string(&mut s)?;
        input = Input::Some(s);
    }

    let stdout = std::io::stdout();

    let root_box = match input {
        Input::Some(data) =>
            nice_tree::parser::parse(&data)?,
        Input::Random{ full_percent, max_levels } =>
            nice_tree::Node::generate_random(full_percent, max_levels),
        Input::None => {
            return Err(MyError::from("No input specified."));
        }
    };

    let mut output_str = String::new();
    root_box.draw_to_string(&mut output_str);
    
    let mut writer: Box<dyn io::Write> = match output {
        Output::StdOut => Box::new(stdout.lock()),
        Output::File(file_path) => Box::new(std::fs::File::create(file_path)?),
    };
    writer.write_all(output_str.as_bytes())?;
    Ok(())
}
