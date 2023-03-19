include "cen.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "wceq.mm"
include "w3a.mm"
include "wss.mm"
include "simp2.mm"
include "wb.mm"
include "enfi.mm"
include "3ad2ant1.mm"
include "mpbid.mm"
include "unfi.mm"
include "syl2anc.mm"
include "ssun1.mm"
include "a1i.mm"
include "simp3.mm"
include "ensymd.mm"
include "fisseneq.mm"
include "syl3anc.mm"
include "ssun2.mm"
include "simp1.mm"
include "entr.mm"
include "eqtr4d.mm"
include "3expia.mm"
include "enrefg.mm"
include "adantl.mm"
include "unidm.mm"
include "uneq2.mm"
include "syl5eqr.mm"
include "breq1d.mm"
include "syl5ibcom.mm"
include "impbid.mm"

theorem fiuneneq
  let cA: class A
  let cB: class B


  assert |- ( ( A ~~ B /\ A e. Fin ) -> ( ( A u. B ) ~~ A <-> A = B ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cA
    cfn
    wcel
    #
    wa
    #
    cA
    cB
    cun
    #
    cA
    cen
    wbr
    #
    cA
    cB
    wceq
    #
    @0
    @1
    @4
    @5
    @0
    @1
    @4
    w3a
    #
    cA
    @3
    cB
    @6
    @3
    cfn
    wcel
    #
    cA
    @3
    wss
    #
    cA
    @3
    cen
    wbr
    cA
    @3
    wceq
    @6
    @1
    cB
    cfn
    wcel
    #
    @7
    @0
    @1
    @4
    simp2
    #
    @6
    @1
    @9
    @10
    @0
    @1
    @1
    @9
    wb
    @4
    cA
    cB
    enfi
    3ad2ant1
    mpbid
    cA
    cB
    unfi
    syl2anc
    #
    @8
    @6
    cA
    cB
    ssun1
    a1i
    @6
    @3
    cA
    @0
    @1
    @4
    simp3
    #
    ensymd
    cA
    @3
    fisseneq
    syl3anc
    @6
    @7
    cB
    @3
    wss
    #
    cB
    @3
    cen
    wbr
    cB
    @3
    wceq
    @11
    @13
    @6
    cB
    cA
    ssun2
    a1i
    @6
    @3
    cB
    @6
    @4
    @0
    @3
    cB
    cen
    wbr
    @12
    @0
    @1
    @4
    simp1
    @3
    cA
    cB
    entr
    syl2anc
    ensymd
    cB
    @3
    fisseneq
    syl3anc
    eqtr4d
    3expia
    @2
    cA
    cA
    cen
    wbr
    #
    @5
    @4
    @1
    @14
    @0
    cA
    cfn
    enrefg
    adantl
    @5
    cA
    @3
    cA
    cen
    @5
    cA
    cA
    cA
    cun
    @3
    cA
    unidm
    cA
    cB
    cA
    uneq2
    syl5eqr
    breq1d
    syl5ibcom
    impbid
end
