include "wfn.mm"
include "wa.mm"
include "cin.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "crn.mm"
include "wral.mm"
include "w3a.mm"
include "ccom.mm"
include "simpl.mm"
include "elin.mm"
include "sylbi.mm"
include "3ad2ant1.mm"
include "fvco2.mm"
include "syl2an.mm"
include "simpr.mm"
include "fveq2.mm"
include "eqcoms.mm"
include "3ad2ant2.mm"
include "adantl.mm"
include "wi.mm"
include "id.mm"
include "fnfvelrn.mm"
include "syl2anr.mm"
include "ex.mm"
include "anim12d.mm"
include "wb.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "biimpri.mm"
include "syl6bi.mm"
include "sylan9.mm"
include "eqeq12d.mm"
include "rspcva.mm"
include "eqcomd.mm"
include "syl6.mm"
include "com23.mm"
include "3impia.mm"
include "impcom.mm"
include "3eqtrrd.mm"
include "eqtrd.mm"

theorem fvcofneq
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cX: class X

  disjoint F x
  disjoint G x
  disjoint H x
  disjoint K x
  disjoint X x
  assert |- ( ( G Fn A /\ K Fn B ) -> ( ( X e. ( A i^i B ) /\ ( G ` X ) = ( K ` X ) /\ A. x e. ( ran G i^i ran K ) ( F ` x ) = ( H ` x ) ) -> ( ( F o. G ) ` X ) = ( ( H o. K ) ` X ) ) )

  proof
    cG
    cA
    wfn
    #
    cK
    cB
    wfn
    #
    wa
    #
    cX
    cA
    cB
    cin
    wcel
    #
    cX
    cG
    cfv
    #
    cX
    cK
    cfv
    #
    wceq
    #
    vx
    cv
    #
    cF
    cfv
    #
    @7
    cH
    cfv
    #
    wceq
    #
    vx
    cG
    crn
    #
    cK
    crn
    #
    cin
    #
    wral
    #
    w3a
    #
    cX
    cF
    cG
    ccom
    cfv
    #
    cX
    cH
    cK
    ccom
    cfv
    #
    wceq
    @2
    @15
    wa
    #
    @16
    @4
    cF
    cfv
    #
    @17
    @2
    @0
    cX
    cA
    wcel
    #
    @16
    @19
    wceq
    @15
    @0
    @1
    simpl
    @3
    @6
    @20
    @14
    @3
    @20
    cX
    cB
    wcel
    #
    wa
    #
    @20
    cX
    cA
    cB
    elin
    #
    @20
    @21
    simpl
    sylbi
    #
    3ad2ant1
    cA
    cF
    cG
    cX
    fvco2
    syl2an
    @18
    @17
    @5
    cH
    cfv
    #
    @4
    cH
    cfv
    #
    @19
    @2
    @1
    @21
    @17
    @25
    wceq
    @15
    @0
    @1
    simpr
    @3
    @6
    @21
    @14
    @3
    @22
    @21
    @23
    @20
    @21
    simpr
    sylbi
    #
    3ad2ant1
    cB
    cH
    cK
    cX
    fvco2
    syl2an
    @15
    @25
    @26
    wceq
    #
    @2
    @6
    @3
    @28
    @14
    @28
    @5
    @4
    @5
    @4
    cH
    fveq2
    eqcoms
    3ad2ant2
    adantl
    @15
    @2
    @26
    @19
    wceq
    #
    @3
    @6
    @14
    @2
    @29
    wi
    @3
    @6
    wa
    #
    @2
    @14
    @29
    @30
    @2
    @4
    @13
    wcel
    #
    @14
    @29
    wi
    @3
    @2
    @4
    @11
    wcel
    #
    @5
    @12
    wcel
    #
    wa
    #
    @6
    @31
    @3
    @0
    @32
    @1
    @33
    @3
    @0
    @32
    @0
    @0
    @20
    @32
    @3
    @0
    id
    @24
    cA
    cX
    cG
    fnfvelrn
    syl2anr
    ex
    @3
    @1
    @33
    @1
    @1
    @21
    @33
    @3
    @1
    id
    @27
    cB
    cX
    cK
    fnfvelrn
    syl2anr
    ex
    anim12d
    @6
    @34
    @32
    @4
    @12
    wcel
    #
    wa
    #
    @31
    @6
    @33
    @35
    @32
    @33
    @35
    wb
    @5
    @4
    @5
    @4
    @12
    eleq1
    eqcoms
    anbi2d
    @31
    @36
    @4
    @11
    @12
    elin
    biimpri
    syl6bi
    sylan9
    @31
    @14
    @29
    @31
    @14
    wa
    @19
    @26
    @10
    @19
    @26
    wceq
    vx
    @4
    @13
    @7
    @4
    wceq
    @8
    @19
    @9
    @26
    @7
    @4
    cF
    fveq2
    @7
    @4
    cH
    fveq2
    eqeq12d
    rspcva
    eqcomd
    ex
    syl6
    com23
    3impia
    impcom
    3eqtrrd
    eqtrd
    ex
end
