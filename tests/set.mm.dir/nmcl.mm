include "cngp.mm"
include "wcel.mm"
include "cr.mm"
include "nmf.mm"
include "ffvelrnda.mm"

theorem nmcl
  let cA: class A
  let cG: class G
  let cN: class N
  let cX: class X
  assume nmf.x: |- X = ( Base ` G )
  assume nmf.n: |- N = ( norm ` G )


  assert |- ( ( G e. NrmGrp /\ A e. X ) -> ( N ` A ) e. RR )

  proof
    cG
    cngp
    wcel
    cX
    cr
    cA
    cN
    cG
    cN
    cX
    nmf.x
    nmf.n
    nmf
    ffvelrnda
end
