
axiom ax-tgoldbachgt
  let vz: setvar z
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cO: class O
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assume ax-tgoldbachgt.o: |- O = { z e. ZZ | -. 2 || z }
  assume ax-tgoldbachgt.g: |- G = { z e. O | E. p e. Prime E. q e. Prime E. r e. Prime ( ( p e. O /\ q e. O /\ r e. O ) /\ z = ( ( p + q ) + r ) ) }
  assert |- E. m e. NN ( m <_ ( ; 1 0 ^ ; 2 7 ) /\ A. n e. O ( m < n -> n e. G ) )
end
