include "cuo.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "cv.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cc.mm"
include "clo.mm"
include "wf1o.mm"
include "unopf1o.mm"
include "f1of.mm"
include "syl.mm"
include "wa.mm"
include "csp.mm"
include "ccnv.mm"
include "cmul.mm"
include "caddc.mm"
include "simplll.mm"
include "hvmulcl.mm"
include "hvaddcl.mm"
include "sylan.mm"
include "adantll.mm"
include "adantr.mm"
include "simpr.mm"
include "unopadj.mm"
include "syl3anc.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "simplr.mm"
include "cnvunop.mm"
include "3syl.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "adantllr.mm"
include "hiassdi.mm"
include "syl22anc.mm"
include "adantrl.mm"
include "3expa.mm"
include "oveq2d.mm"
include "adantlrl.mm"
include "oveq12d.mm"
include "eqtr2d.mm"
include "3eqtrd.mm"
include "ralrimiva.mm"
include "wb.mm"
include "ffvelrn.mm"
include "sylan2.mm"
include "anassrs.mm"
include "an12s.mm"
include "syl2anc.mm"
include "hial2eq.mm"
include "sylanl1.mm"
include "mpbid.mm"
include "ralrimivva.mm"
include "ellnop.mm"
include "sylanbrc.mm"

theorem unoplin
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( T e. UniOp -> T e. LinOp )

  proof
    cT
    cuo
    wcel
    #
    chil
    chil
    cT
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    csm
    co
    #
    vz
    cv
    #
    cva
    co
    #
    cT
    cfv
    #
    @2
    @3
    cT
    cfv
    #
    csm
    co
    #
    @5
    cT
    cfv
    #
    cva
    co
    #
    wceq
    #
    vz
    chil
    wral
    #
    vy
    chil
    wral
    vx
    cc
    wral
    cT
    clo
    wcel
    @0
    chil
    chil
    cT
    wf1o
    @1
    cT
    unopf1o
    chil
    chil
    cT
    f1of
    syl
    #
    @0
    @13
    vx
    vy
    cc
    chil
    @0
    @2
    cc
    wcel
    #
    @3
    chil
    wcel
    #
    wa
    #
    wa
    #
    @12
    vz
    chil
    @18
    @5
    chil
    wcel
    #
    wa
    #
    @7
    vw
    cv
    #
    csp
    co
    #
    @11
    @21
    csp
    co
    #
    wceq
    #
    vw
    chil
    wral
    #
    @12
    @20
    @24
    vw
    chil
    @20
    @21
    chil
    wcel
    #
    wa
    #
    @22
    @6
    @21
    cT
    ccnv
    #
    cfv
    #
    csp
    co
    #
    @2
    @3
    @29
    csp
    co
    #
    cmul
    co
    #
    @5
    @29
    csp
    co
    #
    caddc
    co
    #
    @23
    @27
    @0
    @6
    chil
    wcel
    #
    @26
    @22
    @30
    wceq
    @0
    @17
    @19
    @26
    simplll
    @20
    @35
    @26
    @17
    @19
    @35
    @0
    @17
    @4
    chil
    wcel
    @19
    @35
    @2
    @3
    hvmulcl
    @4
    @5
    hvaddcl
    sylan
    #
    adantll
    adantr
    @20
    @26
    simpr
    #
    @6
    @21
    cT
    unopadj
    syl3anc
    @27
    @15
    @16
    @19
    @29
    chil
    wcel
    #
    @30
    @34
    wceq
    @18
    @15
    @19
    @26
    @0
    @15
    @16
    simprl
    ad2antrr
    #
    @18
    @16
    @19
    @26
    @0
    @15
    @16
    simprr
    ad2antrr
    @18
    @19
    @26
    simplr
    @0
    @19
    @26
    @38
    @17
    @0
    @26
    @38
    @19
    @0
    chil
    chil
    @21
    @28
    @0
    @28
    cuo
    wcel
    chil
    chil
    @28
    wf1o
    chil
    chil
    @28
    wf
    cT
    cnvunop
    @28
    unopf1o
    chil
    chil
    @28
    f1of
    3syl
    ffvelrnda
    adantlr
    adantllr
    @2
    @3
    @5
    @29
    hiassdi
    syl22anc
    @27
    @23
    @2
    @8
    @21
    csp
    co
    #
    cmul
    co
    #
    @10
    @21
    csp
    co
    #
    caddc
    co
    #
    @34
    @27
    @15
    @8
    chil
    wcel
    #
    @10
    chil
    wcel
    #
    @26
    @23
    @43
    wceq
    @39
    @18
    @44
    @19
    @26
    @0
    @16
    @44
    @15
    @0
    chil
    chil
    @3
    cT
    @14
    ffvelrnda
    adantrl
    ad2antrr
    @0
    @19
    @26
    @45
    @17
    @0
    @19
    wa
    @45
    @26
    @0
    chil
    chil
    @5
    cT
    @14
    ffvelrnda
    adantr
    adantllr
    @37
    @2
    @8
    @10
    @21
    hiassdi
    syl22anc
    @27
    @41
    @32
    @42
    @33
    caddc
    @18
    @26
    @41
    @32
    wceq
    #
    @19
    @0
    @16
    @26
    @46
    @15
    @0
    @16
    wa
    @26
    wa
    @40
    @31
    @2
    cmul
    @0
    @16
    @26
    @40
    @31
    wceq
    @3
    @21
    cT
    unopadj
    3expa
    oveq2d
    adantlrl
    adantlr
    @0
    @19
    @26
    @42
    @33
    wceq
    #
    @17
    @0
    @19
    @26
    @47
    @5
    @21
    cT
    unopadj
    3expa
    adantllr
    oveq12d
    eqtr2d
    3eqtrd
    ralrimiva
    @0
    @1
    @17
    @19
    @25
    @12
    wb
    #
    @14
    @1
    @17
    wa
    #
    @19
    wa
    #
    @7
    chil
    wcel
    #
    @11
    chil
    wcel
    #
    @48
    @1
    @17
    @19
    @51
    @17
    @19
    wa
    @1
    @35
    @51
    @36
    chil
    chil
    @6
    cT
    ffvelrn
    sylan2
    anassrs
    @50
    @9
    chil
    wcel
    #
    @45
    @52
    @49
    @53
    @19
    @15
    @1
    @16
    @53
    @1
    @16
    wa
    @15
    @44
    @53
    chil
    chil
    @3
    cT
    ffvelrn
    @2
    @8
    hvmulcl
    sylan2
    an12s
    adantr
    @1
    @19
    @45
    @17
    chil
    chil
    @5
    cT
    ffvelrn
    adantlr
    @9
    @10
    hvaddcl
    syl2anc
    vw
    @7
    @11
    hial2eq
    syl2anc
    sylanl1
    mpbid
    ralrimiva
    ralrimivva
    vx
    vy
    vz
    cT
    ellnop
    sylanbrc
end
