include "cdm.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "csalg.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "cuni.mm"
include "cres.mm"
include "csumge0.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "cmea.mm"
include "fdm.mm"
include "syl.mm"
include "feq2d.mm"
include "mpbird.mm"
include "eqeltrd.mm"
include "jca.mm"
include "unieq.mm"
include "uni0.mm"
include "a1i.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "sylan9eqr.mm"
include "reseq2.mm"
include "res0.mm"
include "adantl.mm"
include "sge00.mm"
include "eqtr4d.mm"
include "adantlr.mm"
include "wn.mm"
include "cn.mm"
include "csn.mm"
include "cun.mm"
include "wfo.mm"
include "wex.mm"
include "simpll.mm"
include "simplrr.mm"
include "simplrl.mm"
include "wne.mm"
include "neqne.mm"
include "id.mm"
include "cbvdisjv.mm"
include "biimpi.mm"
include "ad2antlr.mm"
include "nnfoctbdj.mm"
include "simpl.mm"
include "simprl.mm"
include "simprr.mm"
include "ciun.mm"
include "cmpt.mm"
include "founiiun0.mm"
include "simplll.mm"
include "fof.mm"
include "wss.mm"
include "elpwi.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "0sal.mm"
include "snssi.mm"
include "unssd.mm"
include "fssd.mm"
include "simpr.mm"
include "syl3anc.mm"
include "adantllr.mm"
include "feqmptd.mm"
include "reseq1d.mm"
include "resmptd.mm"
include "ssequn2.mm"
include "sylib.mm"
include "eqcomd.mm"
include "mpteq1d.mm"
include "3eqtrd.mm"
include "cxad.mm"
include "cvv.mm"
include "nfv.mm"
include "simplr.mm"
include "p0ex.mm"
include "cin.mm"
include "disjsn.mm"
include "biimpri.mm"
include "ad2antrr.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "elsni.mm"
include "ad4ant14.mm"
include "sge0splitmpt.mm"
include "fveq2.mm"
include "sylan2.mm"
include "mpteq2dva.mm"
include "sge0z.mm"
include "oveq2d.mm"
include "fssresd.mm"
include "feq1dd.mm"
include "sge0xrcl.mm"
include "xaddid1d.mm"
include "3eqtrrd.mm"
include "pm2.61dan.mm"
include "nfdisj1.mm"
include "nfan.mm"
include "nnex.mm"
include "eqidd.mm"
include "sylan.mm"
include "sge0fodjrn.mm"
include "eqtr2d.mm"
include "syl21anc.mm"
include "ex.mm"
include "exlimdv.mm"
include "sylc.mm"
include "ralrimiva.mm"
include "jca31.mm"
include "ismea.mm"
include "sylibr.mm"

theorem ismeannd
  let wph: wff ph
  let cS: class S
  let ve: setvar e
  let vn: setvar n
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vk: setvar k
  assume ismeannd.sal: |- ( ph -> S e. SAlg )
  assume ismeannd.mf: |- ( ph -> M : S --> ( 0 [,] +oo ) )
  assume ismeannd.m0: |- ( ph -> ( M ` (/) ) = 0 )
  assume ismeannd.iun: |- ( ( ph /\ e : NN --> S /\ Disj_ n e. NN ( e ` n ) ) -> ( M ` U_ n e. NN ( e ` n ) ) = ( sum^ ` ( n e. NN |-> ( M ` ( e ` n ) ) ) ) )

  disjoint M e
  disjoint M n
  disjoint e n
  disjoint e ph
  disjoint n ph
  disjoint M x
  disjoint M y
  disjoint e x
  disjoint e y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint M w
  disjoint n w
  disjoint w x
  disjoint w y
  disjoint S y
  disjoint ph x
  disjoint ph y
  disjoint ph w
  disjoint k x
  assert |- ( ph -> M e. Meas )

  proof
    wph
    cM
    cdm
    #
    cc0
    cpnf
    cicc
    co
    #
    cM
    wf
    #
    @0
    csalg
    wcel
    #
    wa
    #
    c0
    cM
    cfv
    #
    cc0
    wceq
    #
    wa
    vx
    cv
    #
    com
    cdom
    wbr
    #
    vy
    @7
    vy
    cv
    #
    wdisj
    #
    wa
    #
    @7
    cuni
    #
    cM
    cfv
    #
    cM
    @7
    cres
    #
    csumge0
    cfv
    #
    wceq
    #
    wi
    #
    vx
    @0
    cpw
    #
    wral
    #
    wa
    cM
    cmea
    wcel
    wph
    @4
    @6
    @19
    wph
    @2
    @3
    wph
    @2
    cS
    @1
    cM
    wf
    #
    ismeannd.mf
    wph
    @0
    cS
    @1
    cM
    wph
    @20
    @0
    cS
    wceq
    #
    ismeannd.mf
    cS
    @1
    cM
    fdm
    syl
    #
    feq2d
    mpbird
    wph
    @0
    cS
    csalg
    @22
    ismeannd.sal
    eqeltrd
    jca
    ismeannd.m0
    wph
    @17
    vx
    @18
    wph
    @7
    @18
    wcel
    #
    wa
    #
    @11
    @16
    @24
    @11
    wa
    #
    @7
    c0
    wceq
    #
    @16
    @24
    @26
    @16
    @11
    wph
    @26
    @16
    @23
    wph
    @26
    wa
    #
    @13
    cc0
    @15
    @26
    wph
    @13
    @5
    cc0
    @26
    @12
    c0
    cM
    @26
    @12
    c0
    cuni
    #
    c0
    @7
    c0
    unieq
    @28
    c0
    wceq
    @26
    uni0
    a1i
    eqtrd
    fveq2d
    ismeannd.m0
    sylan9eqr
    @27
    @15
    c0
    csumge0
    cfv
    #
    cc0
    @26
    @15
    @29
    wceq
    wph
    @26
    @14
    c0
    csumge0
    @26
    @14
    cM
    c0
    cres
    #
    c0
    @7
    c0
    cM
    reseq2
    @30
    c0
    wceq
    @26
    cM
    res0
    a1i
    eqtrd
    fveq2d
    adantl
    @29
    cc0
    wceq
    @27
    sge00
    a1i
    eqtrd
    eqtr4d
    adantlr
    adantlr
    @25
    @26
    wn
    #
    wa
    #
    @24
    @10
    wa
    #
    cn
    @7
    c0
    csn
    #
    cun
    #
    ve
    cv
    #
    wfo
    #
    vn
    cn
    vn
    cv
    #
    @36
    cfv
    #
    wdisj
    #
    wa
    #
    ve
    wex
    @16
    @32
    @24
    @10
    @24
    @11
    @31
    simpll
    @24
    @8
    @10
    @31
    simplrr
    jca
    @32
    vw
    ve
    vn
    @7
    @24
    @8
    @10
    @31
    simplrl
    @31
    @7
    c0
    wne
    @25
    @7
    c0
    neqne
    adantl
    @11
    vw
    @7
    vw
    cv
    #
    wdisj
    #
    @24
    @31
    @10
    @43
    @8
    @10
    @43
    vy
    vw
    @7
    @9
    @42
    @9
    @42
    wceq
    id
    cbvdisjv
    biimpi
    adantl
    ad2antlr
    nnfoctbdj
    @33
    @41
    @16
    ve
    @33
    @41
    @16
    @33
    @41
    wa
    @33
    @37
    @40
    @16
    @33
    @41
    simpl
    @33
    @37
    @40
    simprl
    @33
    @37
    @40
    simprr
    @33
    @37
    wa
    @40
    wa
    @13
    vn
    cn
    @39
    ciun
    #
    cM
    cfv
    #
    vn
    cn
    @39
    cM
    cfv
    #
    cmpt
    csumge0
    cfv
    #
    @15
    @37
    @13
    @45
    wceq
    @33
    @40
    @37
    @12
    @44
    cM
    vn
    cn
    @7
    @36
    founiiun0
    fveq2d
    ad2antlr
    @24
    @37
    @40
    @45
    @47
    wceq
    #
    @10
    @24
    @37
    wa
    #
    @40
    wa
    #
    wph
    cn
    cS
    @36
    wf
    #
    @40
    @48
    wph
    @23
    @37
    @40
    simplll
    #
    @49
    @51
    @40
    @49
    cn
    @35
    cS
    @36
    @37
    cn
    @35
    @36
    wf
    @24
    cn
    @35
    @36
    fof
    adantl
    @24
    @35
    cS
    wss
    @37
    @24
    @7
    @34
    cS
    @24
    @7
    @0
    cS
    @23
    @7
    @0
    wss
    wph
    @7
    @0
    elpwi
    adantl
    wph
    @21
    @23
    @22
    adantr
    sseqtrd
    #
    wph
    @34
    cS
    wss
    #
    @23
    wph
    c0
    cS
    wcel
    #
    @54
    wph
    cS
    csalg
    wcel
    @55
    ismeannd.sal
    cS
    0sal
    syl
    #
    c0
    cS
    snssi
    syl
    adantr
    unssd
    #
    adantr
    fssd
    adantr
    @49
    @40
    simpr
    #
    ismeannd.iun
    syl3anc
    adantllr
    @24
    @37
    @40
    @47
    @15
    wceq
    @10
    @50
    @15
    vy
    @35
    @9
    cM
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    @47
    @24
    @15
    @61
    wceq
    #
    @37
    @40
    @24
    c0
    @7
    wcel
    #
    @62
    @24
    @63
    wa
    #
    @14
    @60
    csumge0
    @64
    @14
    vy
    cS
    @59
    cmpt
    #
    @7
    cres
    #
    vy
    @7
    @59
    cmpt
    #
    @60
    @24
    @14
    @66
    wceq
    #
    @63
    wph
    @68
    @23
    wph
    cM
    @65
    @7
    wph
    vy
    cS
    @1
    cM
    ismeannd.mf
    feqmptd
    reseq1d
    adantr
    #
    adantr
    @24
    @66
    @67
    wceq
    @63
    @24
    vy
    cS
    @7
    @59
    @53
    resmptd
    #
    adantr
    @63
    @67
    @60
    wceq
    @24
    @63
    vy
    @7
    @35
    @59
    @63
    @35
    @7
    @63
    @34
    @7
    wss
    @35
    @7
    wceq
    c0
    @7
    snssi
    @34
    @7
    ssequn2
    sylib
    eqcomd
    mpteq1d
    adantl
    3eqtrd
    fveq2d
    @24
    @63
    wn
    #
    wa
    #
    @61
    @67
    csumge0
    cfv
    #
    vy
    @34
    @59
    cmpt
    #
    csumge0
    cfv
    #
    cxad
    co
    #
    @73
    cc0
    cxad
    co
    #
    @15
    @72
    vy
    @7
    @34
    @59
    @18
    cvv
    @72
    vy
    nfv
    wph
    @23
    @71
    simplr
    @34
    cvv
    wcel
    #
    @72
    p0ex
    a1i
    @71
    @7
    @34
    cin
    c0
    wceq
    #
    @24
    @79
    @71
    @7
    c0
    disjsn
    biimpri
    adantl
    @24
    @9
    @7
    wcel
    #
    @59
    @1
    wcel
    #
    @71
    @24
    @80
    wa
    cS
    @1
    @9
    cM
    wph
    @20
    @23
    @80
    ismeannd.mf
    ad2antrr
    @24
    @7
    cS
    @9
    @53
    sselda
    ffvelrnd
    adantlr
    wph
    @9
    @34
    wcel
    #
    @81
    @23
    @71
    wph
    @82
    wa
    @59
    @5
    @1
    @82
    @59
    @5
    wceq
    #
    wph
    @82
    @9
    c0
    cM
    @9
    c0
    elsni
    #
    fveq2d
    adantl
    wph
    @5
    @1
    wcel
    @82
    wph
    cS
    @1
    c0
    cM
    ismeannd.mf
    @56
    ffvelrnd
    adantr
    eqeltrd
    ad4ant14
    sge0splitmpt
    wph
    @76
    @77
    wceq
    @23
    @71
    wph
    @75
    cc0
    @73
    cxad
    wph
    @75
    vy
    @34
    cc0
    cmpt
    #
    csumge0
    cfv
    cc0
    wph
    @74
    @85
    csumge0
    wph
    vy
    @34
    @59
    cc0
    @82
    wph
    @9
    c0
    wceq
    #
    @59
    cc0
    wceq
    #
    @84
    wph
    @86
    wa
    @59
    @5
    cc0
    @86
    @83
    wph
    @9
    c0
    cM
    fveq2
    adantl
    wph
    @6
    @86
    ismeannd.m0
    adantr
    eqtrd
    #
    sylan2
    mpteq2dva
    fveq2d
    wph
    @34
    vy
    cvv
    wph
    vy
    nfv
    @78
    wph
    p0ex
    a1i
    sge0z
    eqtrd
    oveq2d
    ad2antrr
    @24
    @77
    @15
    wceq
    @71
    @24
    @77
    @73
    @15
    @24
    @73
    @24
    @67
    @18
    @7
    wph
    @23
    simpr
    @24
    @7
    @1
    @14
    @67
    @24
    @14
    @66
    @67
    @69
    @70
    eqtrd
    #
    @24
    cS
    @1
    @7
    cM
    wph
    @20
    @23
    ismeannd.mf
    adantr
    @53
    fssresd
    feq1dd
    sge0xrcl
    xaddid1d
    @24
    @15
    @73
    @24
    @14
    @67
    csumge0
    @89
    fveq2d
    eqcomd
    eqtrd
    adantr
    3eqtrrd
    pm2.61dan
    ad2antrr
    @50
    @35
    @59
    cn
    @46
    vy
    vn
    @36
    @39
    cvv
    @50
    vy
    nfv
    @49
    @40
    vn
    @49
    vn
    nfv
    vn
    cn
    @39
    nfdisj1
    nfan
    @9
    @39
    cM
    fveq2
    cn
    cvv
    wcel
    @50
    nnex
    a1i
    @24
    @37
    @40
    simplr
    @58
    @50
    @38
    cn
    wcel
    wa
    @39
    eqidd
    @24
    @9
    @35
    wcel
    #
    @81
    @37
    @40
    @24
    @90
    wa
    cS
    @1
    @9
    cM
    wph
    @20
    @23
    @90
    ismeannd.mf
    ad2antrr
    @24
    @35
    cS
    @9
    @57
    sselda
    ffvelrnd
    ad4ant14
    @50
    wph
    @86
    @87
    @52
    @88
    sylan
    sge0fodjrn
    eqtr2d
    adantllr
    3eqtrd
    syl21anc
    ex
    exlimdv
    sylc
    pm2.61dan
    ex
    ralrimiva
    jca31
    vx
    vy
    cM
    ismea
    sylibr
end
