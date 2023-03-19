include "cc.mm"
include "wcel.mm"
include "cr.mm"
include "crp.mm"
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
include "cpr.mm"
include "reelprrecn.mm"
include "a1i.mm"
include "relogcl.mm"
include "adantl.mm"
include "rpreccl.mm"
include "recn.mm"
include "wa.mm"
include "mulcl.mm"
include "efcl.mm"
include "syl.mm"
include "sylan2.mm"
include "ovexd.mm"
include "cres.mm"
include "dvrelog.mm"
include "wf1o.mm"
include "wf.mm"
include "relogf1o.mm"
include "f1of.mm"
include "mp1i.mm"
include "feqmptd.mm"
include "fvres.mm"
include "mpteq2ia.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "syl5reqr.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "toponmax.mm"
include "wss.mm"
include "cin.mm"
include "wceq.mm"
include "ax-resscn.mm"
include "df-ss.mm"
include "sylib.mm"
include "cnelprrecn.mm"
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
include "eqcomd.mm"
include "3eqtr4a.mm"
include "fveq2.mm"
include "dvmptco.mm"
include "dvmptres3.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "rpcn.mm"
include "cc0.mm"
include "wne.mm"
include "rpne0.mm"
include "cxpefd.mm"
include "mpteq2dva.mm"
include "cxpsubd.mm"
include "cxp1d.mm"
include "cxpcld.mm"
include "divrecd.mm"
include "3eqtrd.mm"
include "rpcnd.mm"
include "mul12d.mm"
include "mulassd.mm"
include "eqtr4d.mm"
include "3eqtr4d.mm"

theorem dvcxp1
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A e. CC -> ( RR _D ( x e. RR+ |-> ( x ^c A ) ) ) = ( x e. RR+ |-> ( A x. ( x ^c ( A - 1 ) ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cr
    vx
    crp
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
    crp
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
    cr
    vx
    crp
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
    crp
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
    #
    cr
    cr
    @4
    @6
    crp
    cvv
    crp
    cr
    cr
    cr
    cc
    cpr
    #
    wcel
    @0
    reelprrecn
    a1i
    #
    @18
    @1
    crp
    wcel
    #
    @2
    cr
    wcel
    @0
    @1
    relogcl
    adantl
    @19
    @7
    crp
    wcel
    @0
    @1
    rpreccl
    adantl
    #
    @13
    cr
    wcel
    #
    @0
    @13
    cc
    wcel
    #
    @15
    cc
    wcel
    #
    @13
    recn
    @0
    @22
    wa
    #
    @14
    cc
    wcel
    @23
    cA
    @13
    mulcl
    #
    @14
    efcl
    syl
    #
    sylan2
    @0
    @21
    wa
    @15
    cA
    cmul
    ovexd
    @0
    vx
    crp
    @7
    cmpt
    cr
    clog
    crp
    cres
    #
    cdv
    co
    cr
    vx
    crp
    @2
    cmpt
    #
    cdv
    co
    vx
    dvrelog
    @0
    @27
    @28
    cr
    cdv
    @0
    @27
    vx
    crp
    @1
    @27
    cfv
    #
    cmpt
    @28
    @0
    vx
    crp
    cr
    @27
    crp
    cr
    @27
    wf1o
    crp
    cr
    @27
    wf
    @0
    relogf1o
    crp
    cr
    @27
    f1of
    mp1i
    feqmptd
    vx
    crp
    @29
    @2
    @1
    crp
    clog
    fvres
    mpteq2ia
    syl6eq
    oveq2d
    syl5reqr
    @0
    vy
    @15
    @16
    cr
    ccnfld
    ctopn
    cfv
    #
    cvv
    cc
    cr
    @30
    eqid
    #
    @18
    @30
    cc
    ctopon
    cfv
    wcel
    cc
    @30
    wcel
    @0
    @30
    @31
    cnfldtopon
    cc
    @30
    toponmax
    mp1i
    @0
    cr
    cc
    wss
    #
    cr
    cc
    cin
    cr
    wceq
    @32
    @0
    ax-resscn
    a1i
    cr
    cc
    df-ss
    sylib
    @26
    @24
    @15
    cA
    cmul
    ovexd
    @0
    vy
    vx
    @14
    cA
    @1
    ce
    cfv
    #
    @33
    cc
    cc
    @15
    @15
    cc
    cc
    cc
    cc
    cc
    @17
    wcel
    @0
    cnelprrecn
    a1i
    #
    @34
    @25
    @0
    @22
    simpl
    @1
    cc
    wcel
    #
    @33
    cc
    wcel
    @0
    @1
    efcl
    adantl
    #
    @36
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
    @34
    @0
    @22
    simpr
    @24
    1cnd
    @0
    vy
    cc
    @34
    dvmptid
    @0
    id
    dvmptcmul
    @0
    vy
    cc
    @37
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
    @33
    cmpt
    #
    cdv
    co
    @38
    dvef
    @0
    @38
    ce
    cc
    cdv
    @0
    ce
    @38
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
    eqcomd
    #
    oveq2d
    @39
    3eqtr4a
    @1
    @14
    ce
    fveq2
    #
    @40
    dvmptco
    dvmptres3
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
    @41
    @15
    @4
    cA
    cmul
    @42
    oveq1d
    dvmptco
    @0
    @10
    @5
    cr
    cdv
    @0
    vx
    crp
    @9
    @4
    @0
    @19
    wa
    #
    @1
    cA
    @19
    @35
    @0
    @1
    rpcn
    adantl
    #
    @19
    @1
    cc0
    wne
    @0
    @1
    rpne0
    adantl
    #
    @0
    @19
    simpl
    #
    cxpefd
    #
    mpteq2dva
    oveq2d
    @0
    vx
    crp
    @12
    @8
    @43
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
    @43
    @11
    @48
    cA
    cmul
    @43
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
    @48
    @43
    @1
    cA
    c1
    @44
    @45
    @46
    @43
    1cnd
    cxpsubd
    @43
    @52
    @1
    @9
    cdiv
    @43
    @1
    @44
    cxp1d
    oveq2d
    @43
    @9
    @1
    @43
    @1
    cA
    @44
    @46
    cxpcld
    #
    @44
    @45
    divrecd
    3eqtrd
    oveq2d
    @43
    @49
    @9
    cA
    @7
    cmul
    co
    cmul
    co
    @51
    @43
    cA
    @9
    @7
    @46
    @53
    @43
    @7
    @20
    rpcnd
    #
    mul12d
    @43
    @9
    cA
    @7
    @53
    @46
    @54
    mulassd
    eqtr4d
    @43
    @50
    @6
    @7
    cmul
    @43
    @9
    @4
    cA
    cmul
    @47
    oveq1d
    oveq1d
    3eqtrd
    mpteq2dva
    3eqtr4d
end
