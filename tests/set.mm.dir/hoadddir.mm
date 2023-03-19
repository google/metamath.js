include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "chot.mm"
include "cfv.mm"
include "chos.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cva.mm"
include "csm.mm"
include "addcl.mm"
include "anim1i.mm"
include "3impa.mm"
include "homval.mm"
include "3expa.mm"
include "sylan.mm"
include "3adantl2.mm"
include "3adantl1.mm"
include "oveq12d.mm"
include "ffvelrn.mm"
include "ax-hvdistr2.mm"
include "syl3an3.mm"
include "3exp.mm"
include "exp4a.mm"
include "3imp1.mm"
include "eqtr4d.mm"
include "homulcl.mm"
include "anim12i.mm"
include "3impdir.mm"
include "hosval.mm"
include "ralrimiva.mm"
include "wb.mm"
include "stoic3.mm"
include "hoaddcl.mm"
include "syl2an.mm"
include "hoeq.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem hoadddir
  let cA: class A
  let cB: class B
  let cT: class T
  let vx: setvar x
  let cU: class U


  assert |- ( ( A e. CC /\ B e. CC /\ T : ~H --> ~H ) -> ( ( A + B ) .op T ) = ( ( A .op T ) +op ( B .op T ) ) )

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
    caddc
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
    cT
    chot
    co
    #
    cB
    cT
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
    @7
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
    @11
    @16
    @7
    @5
    @4
    cT
    cfv
    #
    csm
    co
    #
    @19
    @3
    @5
    cc
    wcel
    #
    @2
    wa
    #
    @15
    @7
    @21
    wceq
    #
    @0
    @1
    @2
    @23
    @0
    @1
    wa
    @22
    @2
    cA
    cB
    addcl
    #
    anim1i
    3impa
    @22
    @2
    @15
    @24
    @5
    @4
    cT
    homval
    3expa
    sylan
    @16
    @19
    cA
    @20
    csm
    co
    #
    cB
    @20
    csm
    co
    #
    cva
    co
    #
    @21
    @16
    @17
    @26
    @18
    @27
    cva
    @0
    @2
    @15
    @17
    @26
    wceq
    #
    @1
    @0
    @2
    @15
    @29
    cA
    @4
    cT
    homval
    3expa
    3adantl2
    @1
    @2
    @15
    @18
    @27
    wceq
    #
    @0
    @1
    @2
    @15
    @30
    cB
    @4
    cT
    homval
    3expa
    3adantl1
    oveq12d
    @0
    @1
    @2
    @15
    @21
    @28
    wceq
    #
    @0
    @1
    @2
    @15
    @31
    @0
    @1
    @2
    @15
    wa
    #
    @31
    @32
    @0
    @1
    @20
    chil
    wcel
    @31
    chil
    chil
    @4
    cT
    ffvelrn
    cA
    cB
    @20
    ax-hvdistr2
    syl3an3
    3exp
    exp4a
    3imp1
    eqtr4d
    eqtr4d
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
    @19
    wceq
    #
    @0
    @2
    @1
    @35
    @0
    @2
    wa
    #
    @33
    @1
    @2
    wa
    #
    @34
    cA
    cT
    homulcl
    #
    cB
    cT
    homulcl
    #
    anim12i
    3impdir
    @33
    @34
    @15
    @36
    @4
    @8
    @9
    hosval
    3expa
    sylan
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
    @10
    wf
    #
    @13
    @14
    wb
    @0
    @1
    @22
    @2
    @41
    @25
    @5
    cT
    homulcl
    stoic3
    @0
    @2
    @1
    @42
    @37
    @33
    @34
    @42
    @38
    @39
    @40
    @8
    @9
    hoaddcl
    syl2an
    3impdir
    vx
    @6
    @10
    hoeq
    syl2anc
    mpbid
end
