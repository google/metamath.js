include "cc.mm"
include "wcel.mm"
include "clo.mm"
include "chil.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "chot.mm"
include "co.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "csm.mm"
include "simpl1.mm"
include "simpl3.mm"
include "simpr.mm"
include "homval.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "homulcl.mm"
include "3adant2.mm"
include "fvco3.mm"
include "sylan.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "lnopf.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "fco.mm"
include "adantr.mm"
include "simpl2.mm"
include "ffvelrnda.mm"
include "lnopmul.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"
include "wb.mm"
include "simp1.mm"
include "hoeq.mm"
include "mpbid.mm"

theorem homco2
  let cA: class A
  let cT: class T
  let cU: class U
  let vx: setvar x


  assert |- ( ( A e. CC /\ T e. LinOp /\ U : ~H --> ~H ) -> ( T o. ( A .op U ) ) = ( A .op ( T o. U ) ) )

  proof
    cA
    cc
    wcel
    #
    cT
    clo
    wcel
    #
    chil
    chil
    cU
    wf
    #
    w3a
    #
    vx
    cv
    #
    cT
    cA
    cU
    chot
    co
    #
    ccom
    #
    cfv
    #
    @4
    cA
    cT
    cU
    ccom
    #
    chot
    co
    #
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    #
    @6
    @9
    wceq
    #
    @3
    @11
    vx
    chil
    @3
    @4
    chil
    wcel
    #
    wa
    #
    @4
    @5
    cfv
    #
    cT
    cfv
    #
    cA
    @4
    cU
    cfv
    #
    csm
    co
    #
    cT
    cfv
    #
    @7
    @10
    @15
    @16
    @19
    cT
    @15
    @0
    @2
    @14
    @16
    @19
    wceq
    @0
    @1
    @2
    @14
    simpl1
    #
    @0
    @1
    @2
    @14
    simpl3
    #
    @3
    @14
    simpr
    #
    cA
    @4
    cU
    homval
    syl3anc
    fveq2d
    @3
    chil
    chil
    @5
    wf
    #
    @14
    @7
    @17
    wceq
    @0
    @2
    @24
    @1
    cA
    cU
    homulcl
    3adant2
    #
    chil
    chil
    @4
    cT
    @5
    fvco3
    sylan
    @15
    cA
    @4
    @8
    cfv
    #
    csm
    co
    #
    cA
    @18
    cT
    cfv
    #
    csm
    co
    #
    @10
    @20
    @15
    @26
    @28
    cA
    csm
    @15
    @2
    @14
    @26
    @28
    wceq
    @22
    @23
    chil
    chil
    @4
    cT
    cU
    fvco3
    syl2anc
    oveq2d
    @15
    @0
    chil
    chil
    @8
    wf
    #
    @14
    @10
    @27
    wceq
    @21
    @3
    @30
    @14
    @3
    chil
    chil
    cT
    wf
    #
    @2
    @30
    @1
    @0
    @31
    @2
    cT
    lnopf
    3ad2ant2
    #
    @0
    @1
    @2
    simp3
    #
    chil
    chil
    chil
    cT
    cU
    fco
    syl2anc
    #
    adantr
    @23
    cA
    @4
    @8
    homval
    syl3anc
    @15
    @1
    @0
    @18
    chil
    wcel
    @20
    @29
    wceq
    @0
    @1
    @2
    @14
    simpl2
    @21
    @3
    chil
    chil
    @4
    cU
    @33
    ffvelrnda
    cA
    @18
    cT
    lnopmul
    syl3anc
    3eqtr4d
    3eqtr4d
    ralrimiva
    @3
    chil
    chil
    @6
    wf
    #
    chil
    chil
    @9
    wf
    #
    @12
    @13
    wb
    @3
    @31
    @24
    @35
    @32
    @25
    chil
    chil
    chil
    cT
    @5
    fco
    syl2anc
    @3
    @0
    @30
    @36
    @0
    @1
    @2
    simp1
    @34
    cA
    @8
    homulcl
    syl2anc
    vx
    @6
    @9
    hoeq
    syl2anc
    mpbid
end
