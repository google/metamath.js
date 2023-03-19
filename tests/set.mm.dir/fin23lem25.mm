include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "wo.mm"
include "w3a.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "wpss.mm"
include "dfpss2.mm"
include "csdm.mm"
include "php3.mm"
include "sdomnen.mm"
include "syl.mm"
include "ex.mm"
include "syl5bir.mm"
include "adantl.mm"
include "expd.mm"
include "eqcom.mm"
include "notbii.mm"
include "anbi2i.mm"
include "bitri.mm"
include "ensym.mm"
include "nsyl.mm"
include "adantr.mm"
include "jaod.mm"
include "3impia.mm"
include "con4d.mm"
include "eqeng.mm"
include "3ad2ant1.mm"
include "impbid.mm"

theorem fin23lem25
  let cA: class A
  let cB: class B


  assert |- ( ( A e. Fin /\ B e. Fin /\ ( A C_ B \/ B C_ A ) ) -> ( A ~~ B <-> A = B ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cfn
    wcel
    #
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wo
    #
    w3a
    #
    cA
    cB
    cen
    wbr
    #
    cA
    cB
    wceq
    #
    @5
    @7
    @6
    @0
    @1
    @4
    @7
    wn
    #
    @6
    wn
    #
    wi
    #
    @0
    @1
    wa
    #
    @2
    @10
    @3
    @11
    @2
    @8
    @9
    @1
    @2
    @8
    wa
    #
    @9
    wi
    @0
    @12
    cA
    cB
    wpss
    #
    @1
    @9
    cA
    cB
    dfpss2
    @1
    @13
    @9
    @1
    @13
    wa
    cA
    cB
    csdm
    wbr
    @9
    cB
    cA
    php3
    cA
    cB
    sdomnen
    syl
    ex
    syl5bir
    adantl
    expd
    @11
    @3
    @8
    @9
    @0
    @3
    @8
    wa
    #
    @9
    wi
    @1
    @14
    cB
    cA
    wpss
    #
    @0
    @9
    @15
    @3
    cB
    cA
    wceq
    #
    wn
    #
    wa
    @14
    cB
    cA
    dfpss2
    @17
    @8
    @3
    @16
    @7
    cB
    cA
    eqcom
    notbii
    anbi2i
    bitri
    @0
    @15
    @9
    @0
    @15
    wa
    cB
    cA
    csdm
    wbr
    #
    @9
    cA
    cB
    php3
    @18
    cB
    cA
    cen
    wbr
    @6
    cB
    cA
    sdomnen
    cA
    cB
    ensym
    nsyl
    syl
    ex
    syl5bir
    adantr
    expd
    jaod
    3impia
    con4d
    @0
    @1
    @7
    @6
    wi
    @4
    cA
    cB
    cfn
    eqeng
    3ad2ant1
    impbid
end
