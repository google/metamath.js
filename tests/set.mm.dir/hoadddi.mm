include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "chos.mm"
include "co.mm"
include "chot.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "csm.mm"
include "cva.mm"
include "simpl1.mm"
include "ffvelrn.mm"
include "3ad2antl2.mm"
include "3ad2antl3.mm"
include "ax-hvdistr1.mm"
include "syl3anc.mm"
include "hosval.mm"
include "oveq2d.mm"
include "3expa.mm"
include "3adantl1.mm"
include "homval.mm"
include "3adantl3.mm"
include "3adantl2.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "hoaddcl.mm"
include "anim2i.mm"
include "3impb.mm"
include "sylan.mm"
include "homulcl.mm"
include "anim12i.mm"
include "3impdi.mm"
include "ralrimiva.mm"
include "wb.mm"
include "sylan2.mm"
include "syl2an.mm"
include "hoeq.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem hoadddi
  let cA: class A
  let cT: class T
  let cU: class U
  let vx: setvar x
  let cB: class B


  assert |- ( ( A e. CC /\ T : ~H --> ~H /\ U : ~H --> ~H ) -> ( A .op ( T +op U ) ) = ( ( A .op T ) +op ( A .op U ) ) )

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
    cU
    chos
    co
    #
    chot
    co
    #
    cfv
    #
    @4
    cA
    cT
    chot
    co
    #
    cA
    cU
    chot
    co
    #
    chos
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
    @10
    wceq
    #
    @3
    @12
    vx
    chil
    @3
    @4
    chil
    wcel
    #
    wa
    #
    cA
    @4
    @5
    cfv
    #
    csm
    co
    #
    @4
    @8
    cfv
    #
    @4
    @9
    cfv
    #
    cva
    co
    #
    @7
    @11
    @16
    cA
    @4
    cT
    cfv
    #
    @4
    cU
    cfv
    #
    cva
    co
    #
    csm
    co
    #
    cA
    @22
    csm
    co
    #
    cA
    @23
    csm
    co
    #
    cva
    co
    #
    @18
    @21
    @16
    @0
    @22
    chil
    wcel
    #
    @23
    chil
    wcel
    #
    @25
    @28
    wceq
    @0
    @1
    @2
    @15
    simpl1
    @1
    @0
    @15
    @29
    @2
    chil
    chil
    @4
    cT
    ffvelrn
    3ad2antl2
    @2
    @0
    @15
    @30
    @1
    chil
    chil
    @4
    cU
    ffvelrn
    3ad2antl3
    cA
    @22
    @23
    ax-hvdistr1
    syl3anc
    @1
    @2
    @15
    @18
    @25
    wceq
    #
    @0
    @1
    @2
    @15
    @31
    @1
    @2
    @15
    w3a
    @17
    @24
    cA
    csm
    @4
    cT
    cU
    hosval
    oveq2d
    3expa
    3adantl1
    @16
    @19
    @26
    @20
    @27
    cva
    @0
    @1
    @15
    @19
    @26
    wceq
    #
    @2
    @0
    @1
    @15
    @32
    cA
    @4
    cT
    homval
    3expa
    3adantl3
    @0
    @2
    @15
    @20
    @27
    wceq
    #
    @1
    @0
    @2
    @15
    @33
    cA
    @4
    cU
    homval
    3expa
    3adantl2
    oveq12d
    3eqtr4d
    @3
    @0
    chil
    chil
    @5
    wf
    #
    wa
    #
    @15
    @7
    @18
    wceq
    #
    @0
    @1
    @2
    @35
    @1
    @2
    wa
    #
    @34
    @0
    cT
    cU
    hoaddcl
    #
    anim2i
    3impb
    @0
    @34
    @15
    @36
    cA
    @4
    @5
    homval
    3expa
    sylan
    @3
    chil
    chil
    @8
    wf
    #
    chil
    chil
    @9
    wf
    #
    wa
    #
    @15
    @11
    @21
    wceq
    #
    @0
    @1
    @2
    @41
    @0
    @1
    wa
    #
    @39
    @0
    @2
    wa
    #
    @40
    cA
    cT
    homulcl
    #
    cA
    cU
    homulcl
    #
    anim12i
    3impdi
    @39
    @40
    @15
    @42
    @4
    @8
    @9
    hosval
    3expa
    sylan
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
    @10
    wf
    #
    @13
    @14
    wb
    @0
    @1
    @2
    @47
    @37
    @0
    @34
    @47
    @38
    cA
    @5
    homulcl
    sylan2
    3impb
    @0
    @1
    @2
    @48
    @43
    @39
    @40
    @48
    @44
    @45
    @46
    @8
    @9
    hoaddcl
    syl2an
    3impdi
    vx
    @6
    @10
    hoeq
    syl2anc
    mpbid
end
