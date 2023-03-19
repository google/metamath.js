include "wcel.mm"
include "w3a.mm"
include "cvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "uspgrloopvtx.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "ciedg.mm"
include "csn.mm"
include "cop.mm"
include "uspgrloopiedg.mm"
include "3adant3.mm"
include "1loopgrnb0.mm"

theorem uspgrloopnb0
  let cA: class A
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume uspgrloopvtx.g: |- G = <. V , { <. A , { N } >. } >.


  assert |- ( ( V e. W /\ A e. X /\ N e. V ) -> ( G NeighbVtx N ) = (/) )

  proof
    cV
    cW
    wcel
    #
    cA
    cX
    wcel
    #
    cN
    cV
    wcel
    #
    w3a
    cA
    cG
    cN
    cV
    cX
    @0
    @1
    cG
    cvtx
    cfv
    cV
    wceq
    @2
    cA
    cG
    cN
    cV
    cW
    uspgrloopvtx.g
    uspgrloopvtx
    3ad2ant1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    @0
    @1
    cG
    ciedg
    cfv
    cA
    cN
    csn
    cop
    csn
    wceq
    @2
    cA
    cG
    cN
    cV
    cW
    cX
    uspgrloopvtx.g
    uspgrloopiedg
    3adant3
    1loopgrnb0
end
