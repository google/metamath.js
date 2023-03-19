include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "ccos.mm"
include "cfv.mm"
include "cmpt.mm"
include "cdv.mm"
include "csin.mm"
include "cneg.mm"
include "ccom.mm"
include "cof.mm"
include "mulcl.mm"
include "eqidd.mm"
include "wf.mm"
include "cosf.mm"
include "a1i.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "cr.mm"
include "cpr.mm"
include "cnelprrecn.mm"
include "eqid.mm"
include "fmptd.mm"
include "cdm.mm"
include "wceq.mm"
include "dvcos.mm"
include "dmeqi.mm"
include "dmmptg.mm"
include "sincl.mm"
include "negcld.mm"
include "mprg.mm"
include "eqtri.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "simpl.mm"
include "wa.mm"
include "0red.mm"
include "id.mm"
include "dvmptc.mm"
include "simpr.mm"
include "1red.mm"
include "dvmptid.mm"
include "dvmptmul.mm"
include "dmeqd.mm"
include "cvv.mm"
include "ovex.mm"
include "syl6eq.mm"
include "dvcof.mm"
include "cin.mm"
include "negeqd.mm"
include "oveq1d.mm"
include "cnex.mm"
include "mptex.mm"
include "offval3.mm"
include "mp2an.mm"
include "wral.mm"
include "sincld.mm"
include "ralrimiva.mm"
include "syl.mm"
include "ineq12d.mm"
include "inidm.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "adantl.mm"
include "negex.mm"
include "fvmptd.mm"
include "mul02.mm"
include "mulid2.mm"
include "oveqan12rd.mm"
include "addid2.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "oveq12d.mm"
include "mulcomd.mm"
include "syldan.mm"
include "mpteq12dva.mm"
include "3eqtrd.mm"
include "cbvmptv.mm"

theorem dvcosax
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vk: setvar k

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint k x
  assert |- ( A e. CC -> ( CC _D ( x e. CC |-> ( cos ` ( A x. x ) ) ) ) = ( x e. CC |-> ( A x. -u ( sin ` ( A x. x ) ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cc
    vx
    cc
    cA
    vx
    cv
    #
    cmul
    co
    #
    ccos
    cfv
    #
    cmpt
    #
    cdv
    co
    #
    vy
    cc
    cA
    cA
    vy
    cv
    #
    cmul
    co
    #
    csin
    cfv
    #
    cneg
    #
    cmul
    co
    #
    cmpt
    #
    vx
    cc
    cA
    @2
    csin
    cfv
    #
    cneg
    #
    cmul
    co
    #
    cmpt
    @0
    @5
    cc
    ccos
    vx
    cc
    @2
    cmpt
    #
    ccom
    #
    cdv
    co
    cc
    ccos
    cdv
    co
    #
    @15
    ccom
    #
    cc
    @15
    cdv
    co
    #
    cmul
    cof
    #
    co
    #
    @11
    @0
    @4
    @16
    cc
    cdv
    @0
    @16
    @4
    @0
    vx
    vy
    cc
    cc
    @2
    @6
    ccos
    cfv
    @3
    @15
    ccos
    cA
    @1
    mulcl
    #
    @0
    @15
    eqidd
    #
    @0
    vy
    cc
    cc
    ccos
    cc
    cc
    ccos
    wf
    @0
    cosf
    a1i
    #
    feqmptd
    @6
    @2
    ccos
    fveq2
    fmptco
    eqcomd
    oveq2d
    @0
    cc
    cc
    ccos
    @15
    cc
    cc
    cc
    cr
    cc
    cpr
    wcel
    @0
    cnelprrecn
    a1i
    #
    @25
    @24
    @0
    vx
    cc
    @2
    cc
    @15
    @22
    @15
    eqid
    fmptd
    @17
    cdm
    #
    cc
    wceq
    @0
    @26
    vx
    cc
    @1
    csin
    cfv
    #
    cneg
    #
    cmpt
    #
    cdm
    #
    cc
    @17
    @29
    vx
    dvcos
    dmeqi
    @28
    cc
    wcel
    @30
    cc
    wceq
    vx
    cc
    vx
    cc
    @28
    cc
    dmmptg
    @1
    cc
    wcel
    #
    @27
    @1
    sincl
    negcld
    mprg
    eqtri
    a1i
    @0
    @19
    cdm
    #
    vx
    cc
    cc0
    @1
    cmul
    co
    #
    c1
    cA
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    cdm
    #
    cc
    @0
    @19
    @36
    @0
    vx
    cA
    cc0
    @1
    c1
    cc
    cr
    cr
    cc
    @25
    @0
    @31
    simpl
    @0
    @31
    wa
    #
    0red
    @0
    vx
    cA
    cc
    @25
    @0
    id
    dvmptc
    @0
    @31
    simpr
    @38
    1red
    @0
    vx
    cc
    @25
    dvmptid
    dvmptmul
    #
    dmeqd
    @35
    cvv
    wcel
    #
    @37
    cc
    wceq
    vx
    cc
    vx
    cc
    @35
    cvv
    dmmptg
    @40
    @31
    @33
    @34
    caddc
    ovex
    a1i
    mprg
    syl6eq
    #
    dvcof
    @0
    @21
    vx
    cc
    @13
    cmpt
    #
    @19
    @20
    co
    #
    vy
    @42
    cdm
    #
    @32
    cin
    #
    @6
    @42
    cfv
    #
    @6
    @19
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    @11
    @0
    @18
    @42
    @19
    @20
    @0
    vx
    vy
    cc
    cc
    @2
    @6
    csin
    cfv
    #
    cneg
    #
    @13
    @15
    @17
    @22
    @23
    @17
    vy
    cc
    @51
    cmpt
    wceq
    @0
    vy
    dvcos
    a1i
    @6
    @2
    wceq
    @50
    @12
    @6
    @2
    csin
    fveq2
    negeqd
    fmptco
    oveq1d
    @43
    @49
    wceq
    #
    @0
    @42
    cvv
    wcel
    @19
    cvv
    wcel
    @52
    vx
    cc
    @13
    cnex
    mptex
    cc
    @15
    cdv
    ovex
    vy
    cmul
    @42
    @19
    cvv
    cvv
    offval3
    mp2an
    a1i
    @0
    vy
    @45
    @48
    cc
    @10
    @0
    @45
    cc
    cc
    cin
    cc
    @0
    @44
    cc
    @32
    cc
    @0
    @13
    cc
    wcel
    #
    vx
    cc
    wral
    @44
    cc
    wceq
    @0
    @53
    vx
    cc
    @38
    @12
    @38
    @2
    @22
    sincld
    negcld
    ralrimiva
    vx
    cc
    @13
    cc
    dmmptg
    syl
    @41
    ineq12d
    cc
    inidm
    syl6eq
    #
    @0
    @6
    @45
    wcel
    #
    @6
    cc
    wcel
    #
    @48
    @10
    wceq
    @0
    @55
    wa
    @6
    @45
    cc
    @0
    @55
    simpr
    @0
    @45
    cc
    wceq
    @55
    @54
    adantr
    eleqtrd
    @0
    @56
    wa
    #
    @48
    @9
    cA
    cmul
    co
    @10
    @57
    @46
    @9
    @47
    cA
    cmul
    @56
    @46
    @9
    wceq
    @0
    @56
    vx
    @6
    @13
    @9
    cc
    @42
    cvv
    @56
    @42
    eqidd
    @1
    @6
    wceq
    #
    @13
    @9
    wceq
    @56
    @58
    @12
    @8
    @58
    @2
    @7
    csin
    @1
    @6
    cA
    cmul
    oveq2
    fveq2d
    negeqd
    adantl
    @56
    id
    @9
    cvv
    wcel
    @56
    @8
    negex
    a1i
    fvmptd
    adantl
    @57
    vx
    @6
    @35
    cA
    cc
    @19
    cc
    @0
    @19
    @36
    wceq
    @56
    @39
    adantr
    @58
    @57
    @35
    cc0
    @6
    cmul
    co
    #
    @34
    caddc
    co
    #
    cA
    @58
    @33
    @59
    @34
    caddc
    @1
    @6
    cc0
    cmul
    oveq2
    oveq1d
    @57
    @60
    cc0
    cA
    caddc
    co
    #
    cA
    @56
    @0
    @59
    cc0
    @34
    cA
    caddc
    @6
    mul02
    cA
    mulid2
    oveqan12rd
    @0
    @61
    cA
    wceq
    @56
    cA
    addid2
    adantr
    eqtrd
    sylan9eqr
    @0
    @56
    simpr
    @0
    @56
    simpl
    #
    fvmptd
    oveq12d
    @57
    @9
    cA
    @57
    @8
    @57
    @7
    cA
    @6
    mulcl
    sincld
    negcld
    @62
    mulcomd
    eqtrd
    syldan
    mpteq12dva
    3eqtrd
    3eqtrd
    vy
    vx
    cc
    @10
    @14
    @6
    @1
    wceq
    #
    @9
    @13
    cA
    cmul
    @63
    @8
    @12
    @63
    @7
    @2
    csin
    @6
    @1
    cA
    cmul
    oveq2
    fveq2d
    negeqd
    oveq2d
    cbvmptv
    syl6eq
end
