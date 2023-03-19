include "cdv.mm"
include "co.mm"
include "cdm.mm"
include "wcel.mm"
include "cc.mm"
include "wss.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "ccnp.mm"
include "cfv.mm"
include "eldmg.mm"
include "ibi.mm"
include "wa.mm"
include "climc.mm"
include "simpl2.mm"
include "cc0.mm"
include "caddc.mm"
include "cmin.mm"
include "cmpt.mm"
include "ctx.mm"
include "ffvelrnda.mm"
include "crest.mm"
include "cnt.mm"
include "ctop.mm"
include "cuni.mm"
include "cvv.mm"
include "cnfldtop.mm"
include "simpl1.mm"
include "cnex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "resttop.mm"
include "sylancr.mm"
include "simpl3.mm"
include "ctopon.mm"
include "wceq.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "toponuni.mm"
include "syl.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "ntrss2.mm"
include "syl2anc.mm"
include "csn.mm"
include "cdif.mm"
include "cdiv.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "eldv.mm"
include "simprbda.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "adantr.mm"
include "subcld.mm"
include "ssid.mm"
include "a1i.mm"
include "cxp.mm"
include "txtopon.mm"
include "mp2an.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cmul.mm"
include "sstrd.mm"
include "dvlem.mm"
include "ssdifssd.mm"
include "sselda.mm"
include "simplbda.mm"
include "cres.mm"
include "limcresi.mm"
include "difss.mm"
include "resmpt.mm"
include "oveq1i.mm"
include "sseqtri.mm"
include "subidd.mm"
include "ccn.mm"
include "subcn.mm"
include "ccncf.mm"
include "cncfmptid.mm"
include "cncfmptc.mm"
include "syl3anc.mm"
include "cncfmpt2f.mm"
include "oveq1.mm"
include "cnmptlimc.mm"
include "eqeltrrd.mm"
include "sseldi.mm"
include "cop.mm"
include "mulcn.mm"
include "dvcl.mm"
include "0cn.mm"
include "opelxpi.mm"
include "cncnpi.mm"
include "limccnp2.mm"
include "mul01d.mm"
include "simpr.mm"
include "wne.mm"
include "eldifsni.mm"
include "adantl.mm"
include "subne0d.mm"
include "divcan1d.mm"
include "mpteq2dva.mm"
include "oveq1d.mm"
include "3eltr3d.mm"
include "fmptd.mm"
include "limcdif.mm"
include "syl6eq.mm"
include "eleqtrrd.mm"
include "eqidd.mm"
include "addcn.mm"
include "addid2d.mm"
include "npcand.mm"
include "feqmptd.mm"
include "eqtr4d.mm"
include "wb.mm"
include "cnplimc.mm"
include "mpbir2and.mm"
include "ex.mm"
include "exlimdv.mm"
include "imp.mm"
include "sylan2.mm"

theorem dvcnp2
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cJ: class J
  let cK: class K
  let vy: setvar y
  let vz: setvar z
  assume dvcnp.j: |- J = ( K |`t A )
  assume dvcnp.k: |- K = ( TopOpen ` CCfld )


  assert |- ( ( ( S C_ CC /\ F : A --> CC /\ A C_ S ) /\ B e. dom ( S _D F ) ) -> F e. ( ( J CnP K ) ` B ) )

  proof
    cB
    cS
    cF
    cdv
    co
    #
    cdm
    #
    wcel
    #
    cS
    cc
    wss
    #
    cA
    cc
    cF
    wf
    #
    cA
    cS
    wss
    #
    w3a
    #
    cB
    vy
    cv
    #
    @0
    wbr
    #
    vy
    wex
    #
    cF
    cB
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    @2
    @9
    vy
    cB
    @0
    @1
    eldmg
    ibi
    @6
    @9
    @10
    @6
    @8
    @10
    vy
    @6
    @8
    @10
    @6
    @8
    wa
    #
    @10
    @4
    cB
    cF
    cfv
    #
    cF
    cB
    climc
    co
    #
    wcel
    #
    @3
    @4
    @5
    @8
    simpl2
    #
    @11
    cc0
    @12
    caddc
    co
    vz
    cA
    vz
    cv
    #
    cF
    cfv
    #
    @12
    cmin
    co
    #
    @12
    caddc
    co
    #
    cmpt
    #
    cB
    climc
    co
    @12
    @13
    @11
    vz
    cA
    cB
    cc0
    @12
    @18
    @12
    caddc
    cK
    cK
    ctx
    co
    #
    cK
    cc
    cc
    @11
    @16
    cA
    wcel
    #
    wa
    #
    @17
    @12
    @11
    cA
    cc
    @16
    cF
    @15
    ffvelrnda
    #
    @11
    @12
    cc
    wcel
    #
    @22
    @11
    cA
    cc
    cB
    cF
    @15
    @11
    cA
    cK
    cS
    crest
    co
    #
    cnt
    cfv
    cfv
    #
    cA
    cB
    @11
    @26
    ctop
    wcel
    #
    cA
    @26
    cuni
    #
    wss
    @27
    cA
    wss
    @11
    cK
    ctop
    wcel
    cS
    cvv
    wcel
    #
    @28
    cK
    dvcnp.k
    cnfldtop
    @11
    @3
    cc
    cvv
    wcel
    @30
    @3
    @4
    @5
    @8
    simpl1
    #
    cnex
    cS
    cc
    cvv
    ssexg
    sylancl
    cS
    cK
    cvv
    resttop
    sylancr
    @11
    cA
    cS
    @29
    @3
    @4
    @5
    @8
    simpl3
    #
    @11
    @26
    cS
    ctopon
    cfv
    wcel
    #
    cS
    @29
    wceq
    @11
    cK
    cc
    ctopon
    cfv
    wcel
    #
    @3
    @33
    cK
    dvcnp.k
    cnfldtopon
    #
    @31
    cS
    cK
    cc
    resttopon
    sylancr
    cS
    @26
    toponuni
    syl
    sseqtrd
    cA
    @26
    @29
    @29
    eqid
    ntrss2
    syl2anc
    @6
    @8
    cB
    @27
    wcel
    #
    @7
    vz
    cA
    cB
    csn
    #
    cdif
    #
    @18
    @16
    cB
    cmin
    co
    #
    cdiv
    co
    #
    cmpt
    #
    cB
    climc
    co
    wcel
    #
    @6
    vz
    cA
    cB
    @7
    cS
    @26
    cF
    @41
    cK
    @26
    eqid
    dvcnp.k
    @41
    eqid
    @3
    @4
    @5
    simp1
    #
    @3
    @4
    @5
    simp2
    #
    @3
    @4
    @5
    simp3
    #
    eldv
    #
    simprbda
    sseldd
    #
    ffvelrnd
    #
    adantr
    #
    subcld
    #
    @49
    cc
    cc
    wss
    #
    @11
    cc
    ssid
    #
    a1i
    #
    @53
    dvcnp.k
    @21
    cc
    cc
    cxp
    #
    crest
    co
    #
    @21
    @21
    @54
    ctopon
    cfv
    #
    wcel
    #
    @55
    @21
    wceq
    @34
    @34
    @57
    @35
    @35
    cK
    cK
    cc
    cc
    txtopon
    mp2an
    #
    @21
    @56
    @54
    @54
    @21
    @58
    toponunii
    #
    restid
    ax-mp
    eqcomi
    #
    @11
    cc0
    vz
    @38
    @18
    cmpt
    #
    cB
    climc
    co
    #
    vz
    cA
    @18
    cmpt
    #
    cB
    climc
    co
    #
    @11
    @7
    cc0
    cmul
    co
    vz
    @38
    @40
    @39
    cmul
    co
    #
    cmpt
    #
    cB
    climc
    co
    cc0
    @62
    @11
    vz
    @38
    cB
    @7
    cc0
    @40
    @39
    cmul
    @21
    cK
    cc
    cc
    @11
    @16
    cB
    cA
    cF
    @15
    @11
    cA
    cS
    cc
    @32
    @31
    sstrd
    #
    @47
    dvlem
    @11
    @16
    @38
    wcel
    #
    wa
    #
    @16
    cB
    @11
    @38
    cc
    @16
    @11
    cA
    cc
    @37
    @67
    ssdifssd
    sselda
    #
    @11
    cB
    cc
    wcel
    #
    @68
    @11
    cA
    cc
    cB
    @67
    @47
    sseldd
    #
    adantr
    #
    subcld
    #
    @53
    @53
    dvcnp.k
    @60
    @6
    @8
    @36
    @42
    @46
    simplbda
    @11
    vz
    cA
    @39
    cmpt
    #
    cB
    climc
    co
    #
    vz
    @38
    @39
    cmpt
    #
    cB
    climc
    co
    #
    cc0
    @76
    @75
    @38
    cres
    #
    cB
    climc
    co
    @78
    cB
    @38
    @75
    limcresi
    @79
    @77
    cB
    climc
    @38
    cA
    wss
    #
    @79
    @77
    wceq
    cA
    @37
    difss
    #
    vz
    cA
    @38
    @39
    resmpt
    ax-mp
    oveq1i
    sseqtri
    @11
    cB
    cB
    cmin
    co
    #
    cc0
    @76
    @11
    cB
    @72
    subidd
    @11
    vz
    cA
    cB
    cc
    @39
    @82
    @11
    vz
    @16
    cB
    cmin
    cK
    cA
    dvcnp.k
    cmin
    @21
    cK
    ccn
    co
    #
    wcel
    @11
    cK
    dvcnp.k
    subcn
    a1i
    @11
    cA
    cc
    wss
    #
    @51
    vz
    cA
    @16
    cmpt
    cA
    cc
    ccncf
    co
    #
    wcel
    @67
    @52
    vz
    cA
    cc
    cncfmptid
    sylancl
    @11
    @71
    @84
    @51
    vz
    cA
    cB
    cmpt
    @85
    wcel
    @72
    @67
    @53
    vz
    cB
    cA
    cc
    cncfmptc
    syl3anc
    cncfmpt2f
    @47
    @16
    cB
    cB
    cmin
    oveq1
    cnmptlimc
    eqeltrrd
    sseldi
    @11
    cmul
    @83
    wcel
    @7
    cc0
    cop
    #
    @54
    wcel
    #
    cmul
    @86
    @21
    cK
    ccnp
    co
    #
    cfv
    wcel
    cK
    dvcnp.k
    mulcn
    @11
    @7
    cc
    wcel
    cc0
    cc
    wcel
    #
    @87
    @6
    cA
    cB
    @7
    cS
    cF
    @43
    @44
    @45
    dvcl
    #
    0cn
    @7
    cc0
    cc
    cc
    opelxpi
    sylancl
    @86
    cmul
    @21
    cK
    @54
    @59
    cncnpi
    sylancr
    limccnp2
    @11
    @7
    @90
    mul01d
    @11
    @66
    @61
    cB
    climc
    @11
    vz
    @38
    @65
    @18
    @69
    @18
    @39
    @69
    @17
    @12
    @69
    cA
    cc
    @16
    cF
    @11
    @4
    @68
    @15
    adantr
    @69
    @38
    cA
    @16
    @81
    @11
    @68
    simpr
    sseldi
    ffvelrnd
    @11
    @25
    @68
    @48
    adantr
    subcld
    @74
    @69
    @16
    cB
    @70
    @73
    @68
    @16
    cB
    wne
    @11
    @16
    cA
    cB
    eldifsni
    adantl
    subne0d
    divcan1d
    mpteq2dva
    oveq1d
    3eltr3d
    @11
    @64
    @63
    @38
    cres
    #
    cB
    climc
    co
    @62
    @11
    cA
    cB
    @63
    @11
    vz
    cA
    @18
    cc
    @63
    @50
    @63
    eqid
    fmptd
    limcdif
    @91
    @61
    cB
    climc
    @80
    @91
    @61
    wceq
    @81
    vz
    cA
    @38
    @18
    resmpt
    ax-mp
    oveq1i
    syl6eq
    eleqtrrd
    @11
    vz
    cA
    cB
    cc
    @12
    @12
    @11
    @25
    @84
    @51
    vz
    cA
    @12
    cmpt
    @85
    wcel
    @48
    @67
    @53
    vz
    @12
    cA
    cc
    cncfmptc
    syl3anc
    @47
    @16
    cB
    wceq
    @12
    eqidd
    cnmptlimc
    @11
    caddc
    @83
    wcel
    cc0
    @12
    cop
    #
    @54
    wcel
    #
    caddc
    @92
    @88
    cfv
    wcel
    cK
    dvcnp.k
    addcn
    @11
    @89
    @25
    @93
    0cn
    @48
    cc0
    @12
    cc
    cc
    opelxpi
    sylancr
    @92
    caddc
    @21
    cK
    @54
    @59
    cncnpi
    sylancr
    limccnp2
    @11
    @12
    @48
    addid2d
    @11
    @20
    cF
    cB
    climc
    @11
    @20
    vz
    cA
    @17
    cmpt
    cF
    @11
    vz
    cA
    @19
    @17
    @23
    @17
    @12
    @24
    @49
    npcand
    mpteq2dva
    @11
    vz
    cA
    cc
    cF
    @15
    feqmptd
    eqtr4d
    oveq1d
    3eltr3d
    @11
    @84
    cB
    cA
    wcel
    @10
    @4
    @14
    wa
    wb
    @67
    @47
    cA
    cB
    cF
    cJ
    cK
    dvcnp.k
    dvcnp.j
    cnplimc
    syl2anc
    mpbir2and
    ex
    exlimdv
    imp
    sylan2
end
