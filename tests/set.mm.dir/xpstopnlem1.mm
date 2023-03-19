include "c0.mm"
include "cop.mm"
include "csn.mm"
include "cpt.mm"
include "cfv.mm"
include "cuni.mm"
include "c1o.mm"
include "cv.mm"
include "cun.mm"
include "cmpt2.mm"
include "ccom.mm"
include "ctx.mm"
include "co.mm"
include "ccda.mm"
include "ccnv.mm"
include "chmeo.mm"
include "cxp.mm"
include "c1st.mm"
include "c2nd.mm"
include "wcel.mm"
include "wa.mm"
include "wral.mm"
include "wf.mm"
include "ctopon.mm"
include "ccn.mm"
include "txtopon.mm"
include "syl2anc.mm"
include "ctop.mm"
include "cmpt.mm"
include "cvv.mm"
include "eqid.mm"
include "0ex.mm"
include "a1i.mm"
include "pt1hmeo.mm"
include "hmeocn.mm"
include "cntop2.mm"
include "3syl.mm"
include "toptopon.mm"
include "sylib.mm"
include "con0.mm"
include "1on.mm"
include "wceq.mm"
include "opeq2.mm"
include "sneqd.mm"
include "snex.mm"
include "fvmpt.mm"
include "opeq12.mm"
include "syl2an.mm"
include "mpt2eq3ia.mm"
include "toponuni.mm"
include "syl.mm"
include "mpt2eq12.mm"
include "syl5eqr.mm"
include "txhmeo.mm"
include "eqeltrd.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fmpt2.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "anasss.mm"
include "eqidd.mm"
include "vex.mm"
include "op1std.mm"
include "op2ndd.mm"
include "uneq12d.mm"
include "mpt2mpt.mm"
include "eqcomi.mm"
include "cpr.mm"
include "xpscg.mm"
include "mp2an.mm"
include "df-pr.mm"
include "eqtri.mm"
include "syl6eqr.mm"
include "fmpt2co.mm"
include "syl6reqr.mm"
include "cres.mm"
include "c2o.mm"
include "2on.mm"
include "topontop.mm"
include "xpscf.mm"
include "sylanbrc.mm"
include "df2o3.mm"
include "wne.mm"
include "cin.mm"
include "1n0.mm"
include "necomi.mm"
include "disjsn2.mm"
include "mp1i.mm"
include "ptunhmeo.mm"
include "wfn.mm"
include "xpscfn.mm"
include "prid1.mm"
include "eleqtrri.mm"
include "fnressn.mm"
include "sylancl.mm"
include "xpsc0.mm"
include "opeq2d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "unieqd.mm"
include "elexi.mm"
include "prid2.mm"
include "xpsc1.mm"
include "mpt2eq123dv.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "3eltr3d.mm"
include "hmeoco.mm"

theorem xpstopnlem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vz: setvar z
  assume xpstopnlem1.f: |- F = ( x e. X , y e. Y |-> `' ( { x } +c { y } ) )
  assume xpstopnlem1.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume xpstopnlem1.k: |- ( ph -> K e. ( TopOn ` Y ) )

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint x z
  disjoint y z
  disjoint J z
  disjoint K z
  disjoint ph z
  disjoint X z
  disjoint Y z
  assert |- ( ph -> F e. ( ( J tX K ) Homeo ( Xt_ ` `' ( { J } +c { K } ) ) ) )

  proof
    wph
    cF
    vx
    vy
    c0
    cJ
    cop
    #
    csn
    #
    cpt
    cfv
    #
    cuni
    #
    c1o
    cK
    cop
    #
    csn
    #
    cpt
    cfv
    #
    cuni
    #
    vx
    cv
    #
    vy
    cv
    #
    cun
    #
    cmpt2
    #
    vx
    vy
    cX
    cY
    c0
    @8
    cop
    #
    csn
    #
    c1o
    @9
    cop
    #
    csn
    #
    cop
    #
    cmpt2
    #
    ccom
    #
    cJ
    cK
    ctx
    co
    #
    cJ
    csn
    cK
    csn
    ccda
    co
    ccnv
    #
    cpt
    cfv
    #
    chmeo
    co
    #
    wph
    @18
    vx
    vy
    cX
    cY
    @8
    csn
    @9
    csn
    ccda
    co
    ccnv
    #
    cmpt2
    cF
    wph
    vx
    vy
    vz
    cX
    cY
    @3
    @7
    cxp
    #
    @16
    vz
    cv
    #
    c1st
    cfv
    #
    @25
    c2nd
    cfv
    #
    cun
    #
    @23
    @17
    @11
    wph
    @8
    cX
    wcel
    #
    @9
    cY
    wcel
    #
    @16
    @24
    wcel
    #
    wph
    @29
    wa
    @31
    vy
    cY
    wph
    @31
    vy
    cY
    wral
    #
    vx
    cX
    wph
    cX
    cY
    cxp
    #
    @24
    @17
    wf
    #
    @32
    vx
    cX
    wral
    wph
    @19
    @33
    ctopon
    cfv
    wcel
    #
    @2
    @6
    ctx
    co
    #
    @24
    ctopon
    cfv
    wcel
    #
    @17
    @19
    @36
    ccn
    co
    wcel
    #
    @34
    wph
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cK
    cY
    ctopon
    cfv
    #
    wcel
    #
    @35
    xpstopnlem1.j
    xpstopnlem1.k
    cJ
    cK
    cX
    cY
    txtopon
    syl2anc
    wph
    @2
    @3
    ctopon
    cfv
    wcel
    #
    @6
    @7
    ctopon
    cfv
    wcel
    #
    @37
    wph
    @2
    ctop
    wcel
    #
    @43
    wph
    vz
    cX
    c0
    @25
    cop
    #
    csn
    #
    cmpt
    #
    cJ
    @2
    chmeo
    co
    wcel
    @48
    cJ
    @2
    ccn
    co
    wcel
    @45
    wph
    vz
    c0
    cJ
    @2
    cvv
    cX
    @2
    eqid
    c0
    cvv
    wcel
    wph
    0ex
    a1i
    xpstopnlem1.j
    pt1hmeo
    #
    @48
    cJ
    @2
    hmeocn
    @48
    cJ
    @2
    cntop2
    3syl
    @2
    @3
    @3
    eqid
    toptopon
    sylib
    wph
    @6
    ctop
    wcel
    #
    @44
    wph
    vz
    cY
    c1o
    @25
    cop
    #
    csn
    #
    cmpt
    #
    cK
    @6
    chmeo
    co
    wcel
    @53
    cK
    @6
    ccn
    co
    wcel
    @50
    wph
    vz
    c1o
    cK
    @6
    con0
    cY
    @6
    eqid
    c1o
    con0
    wcel
    wph
    1on
    a1i
    xpstopnlem1.k
    pt1hmeo
    #
    @53
    cK
    @6
    hmeocn
    @53
    cK
    @6
    cntop2
    3syl
    @6
    @7
    @7
    eqid
    toptopon
    sylib
    @2
    @6
    @3
    @7
    txtopon
    syl2anc
    wph
    @17
    @19
    @36
    chmeo
    co
    #
    wcel
    #
    @38
    wph
    @17
    vx
    vy
    cJ
    cuni
    #
    cK
    cuni
    #
    @8
    @48
    cfv
    #
    @9
    @53
    cfv
    #
    cop
    #
    cmpt2
    #
    @55
    wph
    @17
    vx
    vy
    cX
    cY
    @61
    cmpt2
    #
    @62
    vx
    vy
    cX
    cY
    @61
    @16
    @29
    @59
    @13
    wceq
    @60
    @15
    wceq
    @61
    @16
    wceq
    @30
    vz
    @8
    @47
    @13
    cX
    @48
    @25
    @8
    wceq
    @46
    @12
    @25
    @8
    c0
    opeq2
    sneqd
    @48
    eqid
    @12
    snex
    #
    fvmpt
    vz
    @9
    @52
    @15
    cY
    @53
    @25
    @9
    wceq
    @51
    @14
    @25
    @9
    c1o
    opeq2
    sneqd
    @53
    eqid
    @14
    snex
    #
    fvmpt
    @59
    @60
    @13
    @15
    opeq12
    syl2an
    mpt2eq3ia
    wph
    cX
    @57
    wceq
    #
    cY
    @58
    wceq
    #
    @63
    @62
    wceq
    wph
    @40
    @66
    xpstopnlem1.j
    cX
    cJ
    toponuni
    syl
    wph
    @42
    @67
    xpstopnlem1.k
    cY
    cK
    toponuni
    syl
    vx
    vy
    cX
    cY
    @57
    @58
    @61
    mpt2eq12
    syl2anc
    syl5eqr
    wph
    vx
    vy
    @48
    @53
    cJ
    cK
    @2
    @6
    @57
    @58
    @57
    eqid
    @58
    eqid
    @49
    @54
    txhmeo
    eqeltrd
    #
    @17
    @19
    @36
    hmeocn
    syl
    @17
    @19
    @36
    @33
    @24
    cnf2
    syl3anc
    vx
    vy
    cX
    cY
    @16
    @24
    @17
    @17
    eqid
    fmpt2
    sylibr
    r19.21bi
    r19.21bi
    anasss
    wph
    @17
    eqidd
    @11
    vz
    @24
    @28
    cmpt
    #
    wceq
    wph
    @69
    @11
    vx
    vy
    vz
    @3
    @7
    @28
    @10
    @25
    @8
    @9
    cop
    wceq
    @26
    @8
    @27
    @9
    @8
    @9
    @25
    vx
    vex
    #
    vy
    vex
    #
    op1std
    @8
    @9
    @25
    @70
    @71
    op2ndd
    uneq12d
    mpt2mpt
    eqcomi
    a1i
    @25
    @16
    wceq
    #
    @28
    @13
    @15
    cun
    #
    @23
    @72
    @26
    @13
    @27
    @15
    @13
    @15
    @25
    @64
    @65
    op1std
    @13
    @15
    @25
    @64
    @65
    op2ndd
    uneq12d
    @23
    @12
    @14
    cpr
    #
    @73
    @8
    cvv
    wcel
    @9
    cvv
    wcel
    @23
    @74
    wceq
    @70
    @71
    @8
    @9
    cvv
    cvv
    xpscg
    mp2an
    @12
    @14
    df-pr
    eqtri
    syl6eqr
    fmpt2co
    xpstopnlem1.f
    syl6reqr
    wph
    @56
    @11
    @36
    @21
    chmeo
    co
    #
    wcel
    @18
    @22
    wcel
    @68
    wph
    vx
    vy
    @20
    c0
    csn
    #
    cres
    #
    cpt
    cfv
    #
    cuni
    #
    @20
    c1o
    csn
    #
    cres
    #
    cpt
    cfv
    #
    cuni
    #
    @10
    cmpt2
    #
    @78
    @82
    ctx
    co
    #
    @21
    chmeo
    co
    @11
    @75
    wph
    vx
    vy
    @76
    @80
    c2o
    @20
    @84
    @21
    @78
    @82
    con0
    @79
    @83
    @79
    eqid
    @83
    eqid
    @21
    eqid
    @78
    eqid
    @82
    eqid
    @84
    eqid
    c2o
    con0
    wcel
    wph
    2on
    a1i
    wph
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    c2o
    ctop
    @20
    wf
    wph
    @40
    @86
    xpstopnlem1.j
    cX
    cJ
    topontop
    syl
    wph
    @42
    @87
    xpstopnlem1.k
    cY
    cK
    topontop
    syl
    ctop
    cJ
    cK
    xpscf
    sylanbrc
    c2o
    @76
    @80
    cun
    #
    wceq
    wph
    c2o
    c0
    c1o
    cpr
    #
    @88
    df2o3
    c0
    c1o
    df-pr
    eqtri
    a1i
    c0
    c1o
    wne
    @76
    @80
    cin
    c0
    wceq
    wph
    c1o
    c0
    1n0
    necomi
    c0
    c1o
    disjsn2
    mp1i
    ptunhmeo
    wph
    vx
    vy
    @79
    @83
    @10
    @3
    @7
    @10
    wph
    @78
    @2
    wph
    @77
    @1
    cpt
    wph
    @77
    c0
    c0
    @20
    cfv
    #
    cop
    #
    csn
    #
    @1
    wph
    @20
    c2o
    wfn
    #
    c0
    c2o
    wcel
    @77
    @92
    wceq
    wph
    @40
    @42
    @93
    xpstopnlem1.j
    xpstopnlem1.k
    cJ
    cK
    @39
    @41
    xpscfn
    syl2anc
    #
    c0
    @89
    c2o
    c0
    c1o
    0ex
    prid1
    df2o3
    eleqtrri
    c2o
    c0
    @20
    fnressn
    sylancl
    wph
    @91
    @0
    wph
    @90
    cJ
    c0
    wph
    @40
    @90
    cJ
    wceq
    xpstopnlem1.j
    cJ
    cK
    @39
    xpsc0
    syl
    opeq2d
    sneqd
    eqtrd
    fveq2d
    #
    unieqd
    wph
    @82
    @6
    wph
    @81
    @5
    cpt
    wph
    @81
    c1o
    c1o
    @20
    cfv
    #
    cop
    #
    csn
    #
    @5
    wph
    @93
    c1o
    c2o
    wcel
    @81
    @98
    wceq
    @94
    c1o
    @89
    c2o
    c0
    c1o
    c1o
    con0
    1on
    elexi
    prid2
    df2o3
    eleqtrri
    c2o
    c1o
    @20
    fnressn
    sylancl
    wph
    @97
    @4
    wph
    @96
    cK
    c1o
    wph
    @42
    @96
    cK
    wceq
    xpstopnlem1.k
    cJ
    cK
    @41
    xpsc1
    syl
    opeq2d
    sneqd
    eqtrd
    fveq2d
    #
    unieqd
    wph
    @10
    eqidd
    mpt2eq123dv
    wph
    @85
    @36
    @21
    chmeo
    wph
    @78
    @2
    @82
    @6
    ctx
    @95
    @99
    oveq12d
    oveq1d
    3eltr3d
    @17
    @11
    @19
    @36
    @21
    hmeoco
    syl2anc
    eqeltrd
end
