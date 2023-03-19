include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cneg.mm"
include "wo.mm"
include "congtr.mm"
include "3expa.mm"
include "orcd.mm"
include "ex.mm"
include "simpll.mm"
include "znegcl.mm"
include "anim12i.mm"
include "ad2antlr.mm"
include "simplll.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simpr.mm"
include "congsym.mm"
include "syl22anc.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "adantr.mm"
include "adantl.mm"
include "neg2subd.mm"
include "eqcomd.mm"
include "breq2d.mm"
include "sylibd.mm"
include "anim2d.mm"
include "imp.mm"
include "syl3anc.mm"
include "olcd.mm"
include "anim2i.mm"
include "anim1i.mm"
include "simpl.mm"
include "an42s.mm"
include "syl12anc.mm"
include "negnegd.mm"
include "oveq2d.mm"
include "syl.mm"
include "eqtr3d.mm"
include "ccased.mm"
include "3impia.mm"

theorem acongtr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) /\ ( ( A || ( B - C ) \/ A || ( B - -u C ) ) /\ ( A || ( C - D ) \/ A || ( C - -u D ) ) ) ) -> ( A || ( B - D ) \/ A || ( B - -u D ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cC
    cz
    wcel
    #
    cD
    cz
    wcel
    #
    wa
    #
    cA
    cB
    cC
    cmin
    co
    cdvds
    wbr
    #
    cA
    cB
    cC
    cneg
    #
    cmin
    co
    cdvds
    wbr
    #
    wo
    cA
    cC
    cD
    cmin
    co
    cdvds
    wbr
    #
    cA
    cC
    cD
    cneg
    #
    cmin
    co
    cdvds
    wbr
    #
    wo
    wa
    cA
    cB
    cD
    cmin
    co
    cdvds
    wbr
    #
    cA
    cB
    @10
    cmin
    co
    cdvds
    wbr
    #
    wo
    #
    @2
    @5
    wa
    #
    @6
    @9
    @8
    @11
    @14
    @15
    @6
    @9
    wa
    #
    @14
    @15
    @16
    wa
    @12
    @13
    @2
    @5
    @16
    @12
    cA
    cB
    cC
    cD
    congtr
    3expa
    orcd
    ex
    @15
    @8
    @9
    wa
    #
    @14
    @15
    @17
    wa
    #
    @13
    @12
    @18
    @2
    @7
    cz
    wcel
    #
    @10
    cz
    wcel
    #
    wa
    #
    @8
    cA
    @7
    @10
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    #
    @13
    @2
    @5
    @17
    simpll
    @5
    @21
    @2
    @17
    @3
    @19
    @4
    @20
    cC
    znegcl
    #
    cD
    znegcl
    #
    anim12i
    #
    ad2antlr
    @15
    @17
    @24
    @15
    @9
    @23
    @8
    @15
    @9
    cA
    cD
    cC
    cmin
    co
    #
    cdvds
    wbr
    #
    @23
    @15
    @9
    @29
    @15
    @9
    wa
    @0
    @3
    @4
    @9
    @29
    @0
    @1
    @5
    @9
    simplll
    @2
    @3
    @4
    @9
    simplrl
    @2
    @3
    @4
    @9
    simplrr
    @15
    @9
    simpr
    cA
    cC
    cD
    congsym
    syl22anc
    ex
    @15
    @28
    @22
    cA
    cdvds
    @15
    @22
    @28
    @5
    @22
    @28
    wceq
    @2
    @5
    cC
    cD
    @3
    cC
    cc
    wcel
    @4
    cC
    zcn
    adantr
    #
    @4
    cD
    cc
    wcel
    @3
    cD
    zcn
    adantl
    #
    neg2subd
    adantl
    eqcomd
    breq2d
    sylibd
    anim2d
    imp
    cA
    cB
    @7
    @10
    congtr
    syl3anc
    olcd
    ex
    @15
    @6
    @11
    wa
    #
    @14
    @15
    @32
    wa
    #
    @13
    @12
    @33
    @2
    @3
    @20
    wa
    #
    @32
    @13
    @2
    @5
    @32
    simpll
    @5
    @34
    @2
    @32
    @4
    @20
    @3
    @26
    anim2i
    ad2antlr
    @15
    @32
    simpr
    cA
    cB
    cC
    @10
    congtr
    syl3anc
    olcd
    ex
    @15
    @8
    @11
    wa
    #
    @14
    @15
    @35
    wa
    #
    @12
    @13
    @36
    @2
    @19
    @4
    wa
    #
    @8
    cA
    @7
    cD
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    #
    @12
    @2
    @5
    @35
    simpll
    @5
    @37
    @2
    @35
    @3
    @19
    @4
    @25
    anim1i
    ad2antlr
    @15
    @35
    @40
    @15
    @11
    @39
    @8
    @15
    @11
    cA
    @10
    cC
    cmin
    co
    #
    cdvds
    wbr
    #
    @39
    @15
    @11
    @42
    @15
    @11
    wa
    @0
    @3
    wa
    #
    @20
    @11
    @42
    @15
    @43
    @11
    @0
    @4
    @1
    @3
    @43
    @0
    @4
    wa
    @0
    @1
    @3
    wa
    @3
    @0
    @4
    simpl
    @1
    @3
    simpr
    anim12i
    an42s
    adantr
    @5
    @20
    @2
    @11
    @4
    @20
    @3
    @26
    adantl
    ad2antlr
    @15
    @11
    simpr
    cA
    cC
    @10
    congsym
    syl12anc
    ex
    @15
    @41
    @38
    cA
    cdvds
    @5
    @41
    @38
    wceq
    @2
    @5
    @10
    @7
    cneg
    #
    cmin
    co
    @41
    @38
    @5
    @44
    cC
    @10
    cmin
    @5
    cC
    @30
    negnegd
    oveq2d
    @5
    cD
    @7
    @31
    @5
    @21
    @7
    cc
    wcel
    #
    @27
    @19
    @45
    @20
    @7
    zcn
    adantr
    syl
    neg2subd
    eqtr3d
    adantl
    breq2d
    sylibd
    anim2d
    imp
    cA
    cB
    @7
    cD
    congtr
    syl3anc
    orcd
    ex
    ccased
    3impia
end
