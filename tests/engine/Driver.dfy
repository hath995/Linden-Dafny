// Port of main.ml: the command-line entry point.
// Parses a regex + string, runs the chosen register engine, prints captures.
// Usage: matcher -regex "(b)|.*" -string "abc" [-array|-list|-tree]
module Driver {
  import opened Std.Wrappers
  import opened RegElkRegex
  import AI = ArrayInterp
  import LI = ListInterp
  import MI = MapInterp
  import PA = Parser

  datatype RegImpl = RegArray | RegList | RegTree

  method run(impl: RegImpl, raw: raw_regex, str: string) returns (res: Option<seq<int>>)
  {
    match impl
    case RegArray => res := AI.full_match(raw, str);
    case RegList => res := LI.full_match(raw, str);
    case RegTree => res := MI.full_match(raw, str);
  }

  method print_result(res: Option<seq<int>>, str: string) {
    match res
    case None => print "NoMatch\n";
    case Some(arr) =>
      var ngroups := |arr| / 2;
      var i := 0;
      while i < ngroups
        invariant 0 <= i <= ngroups
      {
        print "#", i, ": ";
        if 2 * i + 1 < |arr| {
          var sv := arr[2 * i];
          var ev := arr[2 * i + 1];
          if sv < 0 {
            print "Undefined";       // group undefined iff start register unset
          } else {
            // forward captures have sv <= ev; lookbehind captures may be reversed
            var lo := if sv <= ev then sv else ev;
            var hi := if sv <= ev then ev else sv;
            if 0 <= lo <= hi <= |str| {
              print "\"", str[lo..hi], "\"";
            } else {
              print "[", sv, ",", ev, "]";
            }
          }
        }
        print "\n";
        i := i + 1;
      }
  }

  method Main(args: seq<string>)
  {
    var i := 1;
    var rgx: Option<string> := None;
    var s: Option<string> := None;
    var impl := RegList;     // default: list registers (as in main.ml)
    while i < |args|
      decreases |args| - i
    {
      var a := args[i];
      if a == "-regex" && i + 1 < |args| { rgx := Some(args[i + 1]); i := i + 2; }
      else if a == "-string" && i + 1 < |args| { s := Some(args[i + 1]); i := i + 2; }
      else if a == "-array" { impl := RegArray; i := i + 1; }
      else if a == "-tree" { impl := RegTree; i := i + 1; }
      else if a == "-list" { impl := RegList; i := i + 1; }
      else { i := i + 1; }
    }
    if rgx.None? || s.None? {
      print "usage: matcher -regex \"(b)|.*\" -string \"abc\" [-array|-list|-tree]\n";
      return;
    }
    var pr := PA.parse(rgx.value);
    match pr
    case None => print "parse error in regex\n";
    case Some(raw) =>
      var res := run(impl, raw, s.value);
      print_result(res, s.value);
  }
}
