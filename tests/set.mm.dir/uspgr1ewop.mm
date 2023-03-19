include "wcel.mm"
include "w3a.mm"
include "cpr.mm"
include "cs1.mm"
include "cop.mm"
include "cc0.mm"
include "csn.mm"
include "cuspgr.mm"
include "cvv.mm"
include "wceq.mm"
include "prex.mm"
include "s1val.mm"
include "mp1i.mm"
include "opeq2d.mm"
include "wa.mm"
include "simp1.mm"
include "c0ex.mm"
include "a1i.mm"
include "3simpc.mm"
include "uspgr1eop.mm"
include "syl21anc.mm"
include "eqeltrd.mm"

theorem uspgr1ewop
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( V e. W /\ A e. V /\ B e. V ) -> <. V , <" { A , B } "> >. e. USPGraph )

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
    cV
    cA
    cB
    cpr
    #
    cs1
    #
    cop
    cV
    cc0
    @4
    cop
    csn
    #
    cop
    #
    cuspgr
    @3
    @5
    @6
    cV
    @4
    cvv
    wcel
    @5
    @6
    wceq
    @3
    cA
    cB
    prex
    @4
    cvv
    s1val
    mp1i
    opeq2d
    @3
    @0
    cc0
    cvv
    wcel
    #
    @1
    @2
    wa
    @7
    cuspgr
    wcel
    @0
    @1
    @2
    simp1
    @8
    @3
    c0ex
    a1i
    @0
    @1
    @2
    3simpc
    cc0
    cA
    cB
    cV
    cW
    cvv
    uspgr1eop
    syl21anc
    eqeltrd
end
