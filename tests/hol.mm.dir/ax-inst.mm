

axiom ax-inst(hal: type al, vx: var x, vy: var y, ta: term A, tb: term B, tc: term C, tr: term R, ts: term S) {
  assume ax-inst.1: |- "R |= A";
  assume ax-inst.2: |- "T. |= [ ( \\ x : al . B y : al ) = B ]";
  assume ax-inst.3: |- "T. |= [ ( \\ x : al . S y : al ) = S ]";
  assume ax-inst.4: |- "[ x : al = C ] |= [ A = B ]";
  assume ax-inst.5: |- "[ x : al = C ] |= [ R = S ]";

  return '|-' "S |= B";
}
