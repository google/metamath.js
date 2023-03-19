include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "chot.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "csm.mm"
include "wi.mm"
include "mulcl.mm"
include "homval.mm"
include "syl3an1.mm"
include "3expia.mm"
include "3impa.mm"
include "imp.mm"
include "oveq2d.mm"
include "3expa.mm"
include "3adantl1.mm"
include "ffvelrn.mm"
include "ax-hvmulass.mm"
include "syl3an3.mm"
include "exp43.mm"
include "3imp1.mm"
include "eqtr4d.mm"
include "homulcl.mm"
include "syl3an2.mm"
include "3impb.mm"
include "ralrimiva.mm"
include "wb.mm"
include "stoic3.mm"
include "sylan2.mm"
include "hoeq.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem homulass
  let cA: class A
  let cB: class B
  let cT: class T
  let vx: setvar x
  let cU: class U


  assert |- ( ( A e. CC /\ B e. CC /\ T : ~H --> ~H ) -> ( ( A x. B ) .op T ) = ( A .op ( B .op T ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    chil
    chil
    cT
    wf
    #
    w3a
    #
    vx
    cv
    #
    cA
    cB
    cmul
    co
    #
    cT
    chot
    co
    #
    cfv
    #
    @4
    cA
    cB
    cT
    chot
    co
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
    @5
    @4
    cT
    cfv
    #
    csm
    co
    #
    @17
    @3
    @14
    @7
    @19
    wceq
    #
    @0
    @1
    @2
    @14
    @20
    wi
    @0
    @1
    wa
    #
    @2
    @14
    @20
    @21
    @5
    cc
    wcel
    #
    @2
    @14
    @20
    cA
    cB
    mulcl
    #
    @5
    @4
    cT
    homval
    syl3an1
    3expia
    3impa
    imp
    @15
    @17
    cA
    cB
    @18
    csm
    co
    #
    csm
    co
    #
    @19
    @1
    @2
    @14
    @17
    @25
    wceq
    #
    @0
    @1
    @2
    @14
    @26
    @1
    @2
    @14
    w3a
    @16
    @24
    cA
    csm
    cB
    @4
    cT
    homval
    oveq2d
    3expa
    3adantl1
    @0
    @1
    @2
    @14
    @19
    @25
    wceq
    #
    @0
    @1
    @2
    @14
    @27
    @0
    @1
    @2
    @14
    wa
    #
    @27
    @28
    @0
    @1
    @18
    chil
    wcel
    @27
    chil
    chil
    @4
    cT
    ffvelrn
    cA
    cB
    @18
    ax-hvmulass
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
    @29
    wi
    @0
    @1
    @2
    wa
    #
    @14
    @29
    @30
    @0
    chil
    chil
    @8
    wf
    #
    @14
    @29
    cB
    cT
    homulcl
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
    @22
    @2
    @33
    @23
    @5
    cT
    homulcl
    stoic3
    @0
    @1
    @2
    @34
    @30
    @0
    @31
    @34
    @32
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
