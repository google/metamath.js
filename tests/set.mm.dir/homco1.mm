include "cc.mm"
include "wcel.mm"
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
include "fvco3.mm"
include "3ad2antl3.mm"
include "oveq2d.mm"
include "ffvelrn.mm"
include "homval.mm"
include "syl3an3.mm"
include "3expa.mm"
include "exp43.mm"
include "3imp1.mm"
include "eqtr4d.mm"
include "wi.mm"
include "fco.mm"
include "syl3an2.mm"
include "3expia.mm"
include "3impb.mm"
include "imp.mm"
include "ralrimiva.mm"
include "wb.mm"
include "homulcl.mm"
include "stoic3.mm"
include "sylan2.mm"
include "hoeq.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem homco1
  let cA: class A
  let cT: class T
  let cU: class U
  let vx: setvar x
  let cB: class B


  assert |- ( ( A e. CC /\ T : ~H --> ~H /\ U : ~H --> ~H ) -> ( ( A .op T ) o. U ) = ( A .op ( T o. U ) ) )

  proof
    cA
    cc
    wcel
    #
    chil
    chil
    cT
    wf
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
    cA
    cT
    chot
    co
    #
    cU
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
    @7
    cA
    @4
    @8
    cfv
    #
    csm
    co
    #
    @10
    @15
    @7
    @4
    cU
    cfv
    #
    @5
    cfv
    #
    @17
    @2
    @0
    @14
    @7
    @19
    wceq
    @1
    chil
    chil
    @4
    @5
    cU
    fvco3
    3ad2antl3
    @15
    @17
    cA
    @18
    cT
    cfv
    #
    csm
    co
    #
    @19
    @15
    @16
    @20
    cA
    csm
    @2
    @0
    @14
    @16
    @20
    wceq
    @1
    chil
    chil
    @4
    cT
    cU
    fvco3
    3ad2antl3
    oveq2d
    @0
    @1
    @2
    @14
    @19
    @21
    wceq
    #
    @0
    @1
    @2
    @14
    @22
    @0
    @1
    @2
    @14
    wa
    #
    @22
    @23
    @0
    @1
    @18
    chil
    wcel
    @22
    chil
    chil
    @4
    cU
    ffvelrn
    cA
    @18
    cT
    homval
    syl3an3
    3expa
    exp43
    3imp1
    eqtr4d
    eqtr4d
    @3
    @14
    @10
    @17
    wceq
    #
    @0
    @1
    @2
    @14
    @24
    wi
    @0
    @1
    @2
    wa
    #
    @14
    @24
    @25
    @0
    chil
    chil
    @8
    wf
    #
    @14
    @24
    chil
    chil
    chil
    cT
    cU
    fco
    #
    cA
    @4
    @8
    homval
    syl3an2
    3expia
    3impb
    imp
    eqtr4d
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
    @0
    @1
    chil
    chil
    @5
    wf
    @2
    @28
    cA
    cT
    homulcl
    chil
    chil
    chil
    @5
    cU
    fco
    stoic3
    @0
    @1
    @2
    @29
    @25
    @0
    @26
    @29
    @27
    cA
    @8
    homulcl
    sylan2
    3impb
    vx
    @6
    @9
    hoeq
    syl2anc
    mpbid
end
