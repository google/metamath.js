include "cho.mm"
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
include "hmopf.mm"
include "wa.mm"
include "csp.mm"
include "cmul.mm"
include "caddc.mm"
include "simplll.mm"
include "hvmulcl.mm"
include "hvaddcl.mm"
include "sylan.mm"
include "adantll.mm"
include "adantr.mm"
include "simpr.mm"
include "w3a.mm"
include "hmop.mm"
include "eqcomd.mm"
include "syl3anc.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "simplr.mm"
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

theorem hmoplin
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( T e. HrmOp -> T e. LinOp )

  proof
    cT
    cho
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
    cT
    hmopf
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
    cfv
    #
    csp
    co
    #
    @2
    @3
    @28
    csp
    co
    #
    cmul
    co
    #
    @5
    @28
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
    @29
    wceq
    @0
    @17
    @19
    @26
    simplll
    @20
    @34
    @26
    @17
    @19
    @34
    @0
    @17
    @4
    chil
    wcel
    @19
    @34
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
    @0
    @34
    @26
    w3a
    @29
    @22
    @6
    @21
    cT
    hmop
    eqcomd
    syl3anc
    @27
    @15
    @16
    @19
    @28
    chil
    wcel
    #
    @29
    @33
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
    @37
    @17
    @0
    @26
    @37
    @19
    @0
    chil
    chil
    @21
    cT
    @14
    ffvelrnda
    adantlr
    adantllr
    @2
    @3
    @5
    @28
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
    @33
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
    @42
    wceq
    @38
    @18
    @43
    @19
    @26
    @0
    @16
    @43
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
    @44
    @17
    @0
    @19
    wa
    @44
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
    @36
    @2
    @8
    @10
    @21
    hiassdi
    syl22anc
    @27
    @40
    @31
    @41
    @32
    caddc
    @18
    @26
    @40
    @31
    wceq
    #
    @19
    @0
    @16
    @26
    @45
    @15
    @0
    @16
    wa
    @26
    wa
    @39
    @30
    @2
    cmul
    @0
    @16
    @26
    @39
    @30
    wceq
    @0
    @16
    @26
    w3a
    @30
    @39
    @3
    @21
    cT
    hmop
    eqcomd
    3expa
    oveq2d
    adantlrl
    adantlr
    @0
    @19
    @26
    @41
    @32
    wceq
    #
    @17
    @0
    @19
    @26
    @46
    @0
    @19
    @26
    w3a
    @32
    @41
    @5
    @21
    cT
    hmop
    eqcomd
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
    @47
    @1
    @17
    @19
    @50
    @17
    @19
    wa
    @1
    @34
    @50
    @35
    chil
    chil
    @6
    cT
    ffvelrn
    sylan2
    anassrs
    @49
    @9
    chil
    wcel
    #
    @44
    @51
    @48
    @52
    @19
    @15
    @1
    @16
    @52
    @1
    @16
    wa
    @15
    @43
    @52
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
    @44
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
