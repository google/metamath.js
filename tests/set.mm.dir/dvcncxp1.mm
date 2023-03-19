include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cmpt.mm"
include "cdv.mm"
include "c1.mm"
include "cdiv.mm"
include "ccxp.mm"
include "cmin.mm"
include "cvv.mm"
include "cr.mm"
include "cpr.mm"
include "cnelprrecn.mm"
include "a1i.mm"
include "cmnf.mm"
include "cc0.mm"
include "cioc.mm"
include "cdif.mm"
include "difss.mm"
include "eqsstri.mm"
include "sseli.mm"
include "logdmn0.mm"
include "logcld.mm"
include "adantl.mm"
include "reccld.mm"
include "wa.mm"
include "mulcl.mm"
include "efcl.mm"
include "syl.mm"
include "ovexd.mm"
include "cres.mm"
include "dvlog.mm"
include "ccncf.mm"
include "wf.mm"
include "logcn.mm"
include "cncff.mm"
include "mp1i.mm"
include "feqmptd.mm"
include "fvres.mm"
include "mpteq2ia.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "syl5reqr.mm"
include "simpl.mm"
include "simpr.mm"
include "1cnd.mm"
include "dvmptid.mm"
include "id.mm"
include "dvmptcmul.mm"
include "mulid1.mm"
include "mpteq2dv.mm"
include "eqtrd.mm"
include "dvef.mm"
include "eff.mm"
include "3eqtr3a.mm"
include "fveq2.mm"
include "dvmptco.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "wne.mm"
include "cxpefd.mm"
include "mpteq2dva.mm"
include "cxpsubd.mm"
include "cxp1d.mm"
include "cxpcld.mm"
include "divrecd.mm"
include "3eqtrd.mm"
include "mul12d.mm"
include "mulassd.mm"
include "eqtr4d.mm"
include "3eqtr4d.mm"

theorem dvcncxp1
  let vx: setvar x
  let cA: class A
  let cD: class D
  let vy: setvar y
  assume dvcncxp1.d: |- D = ( CC \ ( -oo (,] 0 ) )

  disjoint A x
  disjoint D x
  disjoint x y
  disjoint A y
  disjoint D y
  assert |- ( A e. CC -> ( CC _D ( x e. D |-> ( x ^c A ) ) ) = ( x e. D |-> ( A x. ( x ^c ( A - 1 ) ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cc
    vx
    cD
    cA
    vx
    cv
    #
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmpt
    #
    cdv
    co
    vx
    cD
    @4
    cA
    cmul
    co
    #
    c1
    @1
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    cc
    vx
    cD
    @1
    cA
    ccxp
    co
    #
    cmpt
    #
    cdv
    co
    vx
    cD
    cA
    @1
    cA
    c1
    cmin
    co
    ccxp
    co
    #
    cmul
    co
    #
    cmpt
    @0
    vx
    vy
    @2
    @7
    cA
    vy
    cv
    #
    cmul
    co
    #
    ce
    cfv
    #
    @15
    cA
    cmul
    co
    cc
    cc
    @4
    @6
    cc
    cvv
    cD
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
    @16
    @1
    cD
    wcel
    #
    @2
    cc
    wcel
    @0
    @17
    @1
    cD
    cc
    @1
    cD
    cc
    cmnf
    cc0
    cioc
    co
    #
    cdif
    cc
    dvcncxp1.d
    cc
    @18
    difss
    eqsstri
    sseli
    #
    @1
    cD
    dvcncxp1.d
    logdmn0
    #
    logcld
    adantl
    @17
    @7
    cc
    wcel
    @0
    @17
    @1
    @19
    @20
    reccld
    adantl
    #
    @0
    @13
    cc
    wcel
    #
    wa
    #
    @14
    cc
    wcel
    @15
    cc
    wcel
    cA
    @13
    mulcl
    #
    @14
    efcl
    syl
    @23
    @15
    cA
    cmul
    ovexd
    @0
    vx
    cD
    @7
    cmpt
    cc
    clog
    cD
    cres
    #
    cdv
    co
    cc
    vx
    cD
    @2
    cmpt
    #
    cdv
    co
    vx
    cD
    dvcncxp1.d
    dvlog
    @0
    @25
    @26
    cc
    cdv
    @0
    @25
    vx
    cD
    @1
    @25
    cfv
    #
    cmpt
    @26
    @0
    vx
    cD
    cc
    @25
    @25
    cD
    cc
    ccncf
    co
    wcel
    cD
    cc
    @25
    wf
    @0
    cD
    dvcncxp1.d
    logcn
    cD
    cc
    @25
    cncff
    mp1i
    feqmptd
    vx
    cD
    @27
    @2
    @1
    cD
    clog
    fvres
    mpteq2ia
    syl6eq
    oveq2d
    syl5reqr
    @0
    vy
    vx
    @14
    cA
    @1
    ce
    cfv
    #
    @28
    cc
    cc
    @15
    @15
    cc
    cc
    cc
    cc
    @16
    @16
    @24
    @0
    @22
    simpl
    @1
    cc
    wcel
    #
    @28
    cc
    wcel
    @0
    @1
    efcl
    adantl
    #
    @30
    @0
    cc
    vy
    cc
    @14
    cmpt
    cdv
    co
    vy
    cc
    cA
    c1
    cmul
    co
    #
    cmpt
    vy
    cc
    cA
    cmpt
    @0
    vy
    @13
    c1
    cA
    cc
    cc
    cc
    @16
    @0
    @22
    simpr
    @23
    1cnd
    @0
    vy
    cc
    @16
    dvmptid
    @0
    id
    dvmptcmul
    @0
    vy
    cc
    @31
    cA
    cA
    mulid1
    mpteq2dv
    eqtrd
    @0
    cc
    ce
    cdv
    co
    ce
    cc
    vx
    cc
    @28
    cmpt
    #
    cdv
    co
    @32
    dvef
    @0
    ce
    @32
    cc
    cdv
    @0
    vx
    cc
    cc
    ce
    cc
    cc
    ce
    wf
    @0
    eff
    a1i
    feqmptd
    #
    oveq2d
    @33
    3eqtr3a
    @1
    @14
    ce
    fveq2
    #
    @34
    dvmptco
    @13
    @2
    wceq
    #
    @14
    @3
    ce
    @13
    @2
    cA
    cmul
    oveq2
    fveq2d
    #
    @35
    @15
    @4
    cA
    cmul
    @36
    oveq1d
    dvmptco
    @0
    @10
    @5
    cc
    cdv
    @0
    vx
    cD
    @9
    @4
    @0
    @17
    wa
    #
    @1
    cA
    @17
    @29
    @0
    @19
    adantl
    #
    @17
    @1
    cc0
    wne
    @0
    @20
    adantl
    #
    @0
    @17
    simpl
    #
    cxpefd
    #
    mpteq2dva
    oveq2d
    @0
    vx
    cD
    @12
    @8
    @37
    @12
    cA
    @9
    @7
    cmul
    co
    #
    cmul
    co
    #
    @9
    cA
    cmul
    co
    #
    @7
    cmul
    co
    #
    @8
    @37
    @11
    @42
    cA
    cmul
    @37
    @11
    @9
    @1
    c1
    ccxp
    co
    #
    cdiv
    co
    @9
    @1
    cdiv
    co
    @42
    @37
    @1
    cA
    c1
    @38
    @39
    @40
    @37
    1cnd
    cxpsubd
    @37
    @46
    @1
    @9
    cdiv
    @37
    @1
    @38
    cxp1d
    oveq2d
    @37
    @9
    @1
    @37
    @1
    cA
    @38
    @40
    cxpcld
    #
    @38
    @39
    divrecd
    3eqtrd
    oveq2d
    @37
    @43
    @9
    cA
    @7
    cmul
    co
    cmul
    co
    @45
    @37
    cA
    @9
    @7
    @40
    @47
    @21
    mul12d
    @37
    @9
    cA
    @7
    @47
    @40
    @21
    mulassd
    eqtr4d
    @37
    @44
    @6
    @7
    cmul
    @37
    @9
    @4
    cA
    cmul
    @41
    oveq1d
    oveq1d
    3eqtrd
    mpteq2dva
    3eqtr4d
end
