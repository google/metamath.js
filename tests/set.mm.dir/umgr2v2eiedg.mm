include "wcel.mm"
include "w3a.mm"
include "ciedg.mm"
include "cfv.mm"
include "cc0.mm"
include "cpr.mm"
include "cop.mm"
include "c1.mm"
include "fveq2i.mm"
include "cvv.mm"
include "wceq.mm"
include "simp1.mm"
include "prex.mm"
include "opiedgfv.mm"
include "sylancl.mm"
include "syl5eq.mm"

theorem umgr2v2eiedg
  let cA: class A
  let cB: class B
  let cG: class G
  let cV: class V
  let cW: class W
  assume umgr2v2evtx.g: |- G = <. V , { <. 0 , { A , B } >. , <. 1 , { A , B } >. } >.


  assert |- ( ( V e. W /\ A e. V /\ B e. V ) -> ( iEdg ` G ) = { <. 0 , { A , B } >. , <. 1 , { A , B } >. } )

  proof
    cV
    cW
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    w3a
    #
    cG
    ciedg
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
    @4
    cop
    #
    cpr
    #
    cop
    #
    ciedg
    cfv
    #
    @7
    cG
    @8
    ciedg
    umgr2v2evtx.g
    fveq2i
    @3
    @0
    @7
    cvv
    wcel
    @9
    @7
    wceq
    @0
    @1
    @2
    simp1
    @5
    @6
    prex
    @7
    cV
    cW
    cvv
    opiedgfv
    sylancl
    syl5eq
end
