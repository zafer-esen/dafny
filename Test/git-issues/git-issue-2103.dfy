// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0

datatype DT_<+A> = DT(ret: A)
type DT<A> = r: DT_<A> | true witness *

method Main() {
  var d := DT(3);
  print d, "\n"; // 3
}
