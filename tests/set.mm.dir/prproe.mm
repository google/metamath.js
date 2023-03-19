include "cpr.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "elpri.mm"
include "simprrr.mm"
include "necom.mm"
include "wb.mm"
include "neeq2.mm"
include "eqcoms.mm"
include "biimpcd.mm"
include "sylbi.mm"
include "adantr.mm"
include "impcom.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "eleq1.mm"
include "adantl.mm"
include "prid2g.mm"
include "rspcedvd.mm"
include "ex.mm"
include "simprrl.mm"
include "prid1g.mm"
include "jaoi.mm"
include "syl.mm"
include "3impib.mm"

theorem prproe
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V

  disjoint A v
  disjoint B v
  disjoint C v
  disjoint V v
  assert |- ( ( C e. { A , B } /\ A =/= B /\ ( A e. V /\ B e. V ) ) -> E. v e. ( V \ { C } ) v e. { A , B } )

  proof
    cC
    cA
    cB
    cpr
    #
    wcel
    #
    cA
    cB
    wne
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    wa
    #
    vv
    cv
    #
    @0
    wcel
    #
    vv
    cV
    cC
    csn
    cdif
    #
    wrex
    #
    @1
    cC
    cA
    wceq
    #
    cC
    cB
    wceq
    #
    wo
    @2
    @5
    wa
    #
    @9
    wi
    #
    cC
    cA
    cB
    elpri
    @10
    @13
    @11
    @10
    @12
    @9
    @10
    @12
    wa
    #
    @7
    cB
    @0
    wcel
    #
    vv
    cB
    @8
    @14
    @4
    cB
    cC
    wne
    #
    cB
    @8
    wcel
    @10
    @2
    @3
    @4
    simprrr
    @12
    @10
    @16
    @2
    @10
    @16
    wi
    #
    @5
    @2
    cB
    cA
    wne
    #
    @17
    cA
    cB
    necom
    @10
    @18
    @16
    @18
    @16
    wb
    cA
    cC
    cA
    cC
    cB
    neeq2
    eqcoms
    biimpcd
    sylbi
    adantr
    impcom
    cB
    cV
    cC
    eldifsn
    sylanbrc
    @6
    cB
    wceq
    @7
    @15
    wb
    @14
    @6
    cB
    @0
    eleq1
    adantl
    @12
    @15
    @10
    @5
    @15
    @2
    @4
    @15
    @3
    cA
    cB
    cV
    prid2g
    adantl
    adantl
    adantl
    rspcedvd
    ex
    @11
    @12
    @9
    @11
    @12
    wa
    #
    @7
    cA
    @0
    wcel
    #
    vv
    cA
    @8
    @19
    @3
    cA
    cC
    wne
    #
    cA
    @8
    wcel
    @11
    @2
    @3
    @4
    simprrl
    @12
    @11
    @21
    @2
    @11
    @21
    wi
    @5
    @11
    @2
    @21
    @2
    @21
    wb
    cB
    cC
    cB
    cC
    cA
    neeq2
    eqcoms
    biimpcd
    adantr
    impcom
    cA
    cV
    cC
    eldifsn
    sylanbrc
    @6
    cA
    wceq
    @7
    @20
    wb
    @19
    @6
    cA
    @0
    eleq1
    adantl
    @12
    @20
    @11
    @5
    @20
    @2
    @3
    @20
    @4
    cA
    cB
    cV
    prid1g
    adantr
    adantl
    adantl
    rspcedvd
    ex
    jaoi
    syl
    3impib
end
