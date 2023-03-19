include "wcel.mm"
include "cdiag2.mm"
include "cfv.mm"
include "cid.mm"
include "cxp.mm"
include "cin.mm"
include "c1st.mm"
include "c2nd.mm"
include "wceq.mm"
include "wa.mm"
include "bj-diagval.mm"
include "eleq2d.mm"
include "elin.mm"
include "ancom.mm"
include "bj-elid2.mm"
include "pm5.32i.mm"
include "3bitri.mm"
include "syl6bb.mm"

theorem bj-eldiag
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( B e. ( Diag ` A ) <-> ( B e. ( A X. A ) /\ ( 1st ` B ) = ( 2nd ` B ) ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cA
    cdiag2
    cfv
    #
    wcel
    cB
    cid
    cA
    cA
    cxp
    #
    cin
    #
    wcel
    #
    cB
    @2
    wcel
    #
    cB
    c1st
    cfv
    cB
    c2nd
    cfv
    wceq
    #
    wa
    #
    @0
    @1
    @3
    cB
    cA
    cV
    bj-diagval
    eleq2d
    @4
    cB
    cid
    wcel
    #
    @5
    wa
    @5
    @8
    wa
    @7
    cB
    cid
    @2
    elin
    @8
    @5
    ancom
    @5
    @8
    @6
    cB
    cA
    cA
    bj-elid2
    pm5.32i
    3bitri
    syl6bb
end
