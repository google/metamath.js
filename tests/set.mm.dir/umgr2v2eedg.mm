include "wcel.mm"
include "w3a.mm"
include "cedg.mm"
include "cfv.mm"
include "ciedg.mm"
include "crn.mm"
include "cc0.mm"
include "cpr.mm"
include "cop.mm"
include "c1.mm"
include "csn.mm"
include "wceq.mm"
include "edgval.mm"
include "a1i.mm"
include "umgr2v2eiedg.mm"
include "rneqd.mm"
include "cvv.mm"
include "c0ex.mm"
include "1ex.mm"
include "rnpropg.mm"
include "mp2an.mm"
include "dfsn2.mm"
include "syl6eqr.mm"
include "3eqtrd.mm"

theorem umgr2v2eedg
  let cA: class A
  let cB: class B
  let cG: class G
  let cV: class V
  let cW: class W
  assume umgr2v2evtx.g: |- G = <. V , { <. 0 , { A , B } >. , <. 1 , { A , B } >. } >.


  assert |- ( ( V e. W /\ A e. V /\ B e. V ) -> ( Edg ` G ) = { { A , B } } )

  proof
    cV
    cW
    wcel
    cA
    cV
    wcel
    cB
    cV
    wcel
    w3a
    #
    cG
    cedg
    cfv
    #
    cG
    ciedg
    cfv
    #
    crn
    #
    cc0
    cA
    cB
    cpr
    #
    cop
    c1
    @4
    cop
    cpr
    #
    crn
    #
    @4
    csn
    #
    @1
    @3
    wceq
    @0
    cG
    edgval
    a1i
    @0
    @2
    @5
    cA
    cB
    cG
    cV
    cW
    umgr2v2evtx.g
    umgr2v2eiedg
    rneqd
    @0
    @6
    @4
    @4
    cpr
    #
    @7
    @6
    @8
    wceq
    #
    @0
    cc0
    cvv
    wcel
    c1
    cvv
    wcel
    @9
    c0ex
    1ex
    cc0
    c1
    @4
    @4
    cvv
    cvv
    rnpropg
    mp2an
    a1i
    @4
    dfsn2
    syl6eqr
    3eqtrd
end
