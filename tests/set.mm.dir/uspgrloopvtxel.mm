include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "uspgrloopvtx.mm"
include "wi.mm"
include "eleq2.mm"
include "biimpd.mm"
include "eqcoms.mm"
include "com12.mm"
include "mpan9.mm"

theorem uspgrloopvtxel
  let cA: class A
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  assume uspgrloopvtx.g: |- G = <. V , { <. A , { N } >. } >.


  assert |- ( ( V e. W /\ N e. V ) -> N e. ( Vtx ` G ) )

  proof
    cV
    cW
    wcel
    cG
    cvtx
    cfv
    #
    cV
    wceq
    #
    cN
    cV
    wcel
    #
    cN
    @0
    wcel
    #
    cA
    cG
    cN
    cV
    cW
    uspgrloopvtx.g
    uspgrloopvtx
    @1
    @2
    @3
    @2
    @3
    wi
    cV
    @0
    cV
    @0
    wceq
    @2
    @3
    cV
    @0
    cN
    eleq2
    biimpd
    eqcoms
    com12
    mpan9
end
