include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "wss.mm"
include "cuni.mm"
include "elssuni.mm"
include "wceq.mm"
include "eqid.mm"
include "restuni.mm"
include "sylan2.mm"
include "sseq2d.mm"
include "syl5ibr.mm"
include "pm4.71rd.mm"
include "wb.mm"
include "simpll.mm"
include "simplr.mm"
include "ssid.mm"
include "a1i.mm"
include "simpr.mm"
include "restopnb.mm"
include "syl23anc.mm"
include "pm5.32da.mm"
include "bitr4d.mm"
include "ancom.mm"
include "syl6bb.mm"

theorem restopn2
  let cA: class A
  let cB: class B
  let cJ: class J


  assert |- ( ( J e. Top /\ A e. J ) -> ( B e. ( J |`t A ) <-> ( B e. J /\ B C_ A ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cJ
    wcel
    #
    wa
    #
    cB
    cJ
    cA
    crest
    co
    #
    wcel
    #
    cB
    cA
    wss
    #
    cB
    cJ
    wcel
    #
    wa
    #
    @6
    @5
    wa
    @2
    @4
    @5
    @4
    wa
    @7
    @2
    @4
    @5
    @4
    @5
    @2
    cB
    @3
    cuni
    #
    wss
    cB
    @3
    elssuni
    @2
    cA
    @8
    cB
    @1
    @0
    cA
    cJ
    cuni
    #
    wss
    cA
    @8
    wceq
    cA
    cJ
    elssuni
    cA
    cJ
    @9
    @9
    eqid
    restuni
    sylan2
    sseq2d
    syl5ibr
    pm4.71rd
    @2
    @5
    @6
    @4
    @2
    @5
    wa
    #
    @0
    @1
    @1
    cA
    cA
    wss
    #
    @5
    @6
    @4
    wb
    @0
    @1
    @5
    simpll
    @0
    @1
    @5
    simplr
    #
    @12
    @11
    @10
    cA
    ssid
    a1i
    @2
    @5
    simpr
    cA
    cA
    cB
    cJ
    cJ
    restopnb
    syl23anc
    pm5.32da
    bitr4d
    @5
    @6
    ancom
    syl6bb
end
