include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "cc0.mm"
include "cpr.mm"
include "cop.mm"
include "c1.mm"
include "fveq2i.mm"
include "cvv.mm"
include "wceq.mm"
include "prex.mm"
include "opvtxfv.mm"
include "mpan2.mm"
include "syl5eq.mm"

theorem umgr2v2evtx
  let cA: class A
  let cB: class B
  let cG: class G
  let cV: class V
  let cW: class W
  assume umgr2v2evtx.g: |- G = <. V , { <. 0 , { A , B } >. , <. 1 , { A , B } >. } >.


  assert |- ( V e. W -> ( Vtx ` G ) = V )

  proof
    cV
    cW
    wcel
    #
    cG
    cvtx
    cfv
    cV
    cc0
    cA
    cB
    cpr
    #
    cop
    #
    c1
    @1
    cop
    #
    cpr
    #
    cop
    #
    cvtx
    cfv
    #
    cV
    cG
    @5
    cvtx
    umgr2v2evtx.g
    fveq2i
    @0
    @4
    cvv
    wcel
    @6
    cV
    wceq
    @2
    @3
    prex
    @4
    cV
    cW
    cvv
    opvtxfv
    mpan2
    syl5eq
end
