use std::io::stdin;
use std::io::Read;
use std::fs::File;
use std::string::String;
use std::env::args;

// The Config stores the flag `cat` may have been passed.
// It also dabbles as a small state storing the number of
// lines printed so far.

struct Config
  { show_ends : bool
  , show_tabs : bool
  , nb_outlns : Option<u32>
  }

fn config () -> Config {
  return Config
         { show_ends : false
         , show_tabs : false
         , nb_outlns : None
         }
}

enum Source<'a>
  { STDIN
  , FILE (&'a String)
  }
use self::Source::*;

fn read_from_source (src : &Source) -> Result<String, std::io::Error> {
  let mut str = String::new();
  match src
  { &STDIN     => try! (stdin().read_to_string(&mut str))
  , &FILE (fp) => { let mut src = try! (File::open(fp));
                    try! (src.read_to_string(&mut str))
                  }
  };
  return Ok(str);
}

fn cat_string (cfg : &mut Config, str : &String) -> () {
  for ln in str.lines()
  { let mut ln = ln.to_string();
    if cfg.show_ends { ln.push('$'); }
    if cfg.show_tabs { ln = ln.replace('\t', "^I"); }
    match cfg.nb_outlns
    { None     => ()
    , Some (n) => { ln = format! ("{:>6}  {}", n, ln);
                    cfg.nb_outlns = Some (1+n) }
    }
    print!("{}\n", ln);
  }
}

fn cat_source (mut cfg : &mut Config, src : &Source) -> () {
  match read_from_source (&src)
  { Ok  (str) => cat_string (&mut cfg, &str)
  , Err (err) => print! ("{}\n", err)
  };
}

fn main () {
  let mut cfg = config ();
  let mut fps = Vec::new();
  // read options
  for opt in args().skip(1)
   { match opt.as_ref()
     { "-E" => cfg.show_ends = true
     , "-T" => cfg.show_tabs = true
     , "-A" => { cfg.show_ends = true; cfg.show_tabs = true }
     , "-n" => cfg.nb_outlns = Some (1)
     , _    => fps.push(opt)
     };
   };
  // process the files 
  for fp in fps
   { let src = match fp.as_ref()
               { "-" => STDIN
               , _   => FILE (&fp)
               };
     cat_source (&mut cfg, &src)
   }
}
