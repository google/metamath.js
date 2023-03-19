include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "umgr2v2evtx.mm"
include "eqcom.mm"
include "biimpi.mm"
include "eleq2d.mm"
include "biimpcd.mm"
include "mpan9.mm"

theorem umgr2v2evtxel
  let cA: class A
  let cB: class B
  let cG: class G
  let cV: class V
  let cW: class W
  assume umgr2v2evtx.g: |- G = <. V , { <. 0 , { A , B } >. , <. 1 , { A , B } >. } >.


  assert |- ( ( V e. W /\ A e. V ) -> A e. ( Vtx ` G ) )

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
    cA
    cV
    wcel
    #
    cA
    @0
    wcel
    #
    cA
    cB
    cG
    cV
    cW
    umgr2v2evtx.g
    umgr2v2evtx
    @1
    @2
    @3
    @1
    cV
    @0
    cA
    @1
    cV
    @0
    wceq
    @0
    cV
    eqcom
    biimpi
    eleq2d
    biimpcd
    mpan9
end
