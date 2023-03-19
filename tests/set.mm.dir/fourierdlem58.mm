include "cr.mm"
include "cdv.mm"
include "co.mm"
include "ccncf.mm"
include "wcel.mm"
include "wf.mm"
include "cdm.mm"
include "wss.mm"
include "cv.mm"
include "c2.mm"
include "cdiv.mm"
include "csin.mm"
include "cfv.mm"
include "cmul.mm"
include "wa.mm"
include "cpi.mm"
include "cneg.mm"
include "cicc.mm"
include "pire.mm"
include "a1i.mm"
include "renegcld.mm"
include "iccssred.mm"
include "sselda.mm"
include "sseldd.mm"
include "2re.mm"
include "rehalfcld.mm"
include "resincld.mm"
include "remulcld.mm"
include "2cnd.mm"
include "recnd.mm"
include "halfcld.mm"
include "sincld.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "wceq.mm"
include "eqcom.mm"
include "biimpi.mm"
include "adantl.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "adantll.mm"
include "wn.mm"
include "ad2antrr.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "fourierdlem44.mm"
include "syl2anc.mm"
include "mulne0d.mm"
include "redivcld.mm"
include "fmptd.mm"
include "sstrd.mm"
include "dvfre.mm"
include "cc.mm"
include "cmpt.mm"
include "cof.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "eqidd.mm"
include "offval2.mm"
include "syl6reqr.mm"
include "oveq2d.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "eqid.mm"
include "csn.mm"
include "cdif.mm"
include "mulcld.mm"
include "neneqd.mm"
include "wb.mm"
include "elsng.mm"
include "syl.mm"
include "mtbird.mm"
include "eldifd.mm"
include "c1.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "tgioo2.mm"
include "syl6eleq.mm"
include "dvmptidg.mm"
include "ax-resscn.mm"
include "1cnd.mm"
include "ssid.mm"
include "constcncfg.mm"
include "ccos.mm"
include "cres.mm"
include "cnt.mm"
include "resmptd.mm"
include "eqcomd.mm"
include "recn.mm"
include "fmpti.mm"
include "dvres.mm"
include "syl22anc.mm"
include "ctop.mm"
include "retop.mm"
include "uniretop.mm"
include "isopn3.mm"
include "mpbid.mm"
include "reseq2d.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "id.mm"
include "divrec2d.mm"
include "fveq2d.mm"
include "mpteq2ia.mm"
include "eqtr2i.mm"
include "oveq2i.mm"
include "halfcn.mm"
include "2cn.mm"
include "dvasinbx.mm"
include "mp2an.mm"
include "recidi.mm"
include "oveq12d.mm"
include "halfcl.mm"
include "coscld.mm"
include "mulid2d.mm"
include "eqtrd.mm"
include "eqtri.mm"
include "dmeqi.mm"
include "dmmptg.mm"
include "mprg.mm"
include "sseqtr4i.mm"
include "dvres3.mm"
include "mp4an.mm"
include "reseq1i.mm"
include "3eqtri.mm"
include "resabs1d.mm"
include "3eqtrd.mm"
include "coscn.mm"
include "idcncfg.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "difssd.mm"
include "divcncf.mm"
include "cncfmpt1f.mm"
include "dvdivcncf.mm"
include "cncff.mm"
include "fdm.mm"
include "3syl.mm"
include "feq2d.mm"
include "cncffvrn.mm"
include "mpbird.mm"

theorem fourierdlem58
  let wph: wff ph
  let cA: class A
  let cK: class K
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem58.k: |- K = ( s e. A |-> ( s / ( 2 x. ( sin ` ( s / 2 ) ) ) ) )
  assume fourierdlem58.ass: |- ( ph -> A C_ ( -u _pi [,] _pi ) )
  assume fourierdlem58.0nA: |- ( ph -> -. 0 e. A )
  assume fourierdlem58.4: |- ( ph -> A e. ( topGen ` ran (,) ) )

  disjoint A s
  disjoint ph s
  disjoint k x
  assert |- ( ph -> ( RR _D K ) e. ( A -cn-> RR ) )

  proof
    wph
    cr
    cK
    cdv
    co
    #
    cA
    cr
    ccncf
    co
    wcel
    #
    cA
    cr
    @0
    wf
    #
    wph
    @0
    cdm
    #
    cr
    @0
    wf
    #
    @2
    wph
    cA
    cr
    cK
    wf
    cA
    cr
    wss
    #
    @4
    wph
    vs
    cA
    vs
    cv
    #
    c2
    @6
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cr
    cK
    wph
    @6
    cA
    wcel
    #
    wa
    #
    @6
    @9
    @12
    cpi
    cneg
    #
    cpi
    cicc
    co
    #
    cr
    @6
    @12
    @13
    cpi
    @12
    cpi
    cpi
    cr
    wcel
    #
    @12
    pire
    a1i
    #
    renegcld
    @16
    iccssred
    wph
    cA
    @14
    @6
    fourierdlem58.ass
    sselda
    #
    sseldd
    #
    @12
    c2
    @8
    c2
    cr
    wcel
    @12
    2re
    a1i
    @12
    @7
    @12
    @6
    @18
    rehalfcld
    resincld
    remulcld
    #
    @12
    c2
    @8
    @12
    2cnd
    #
    @12
    @7
    @12
    @6
    @12
    @6
    @18
    recnd
    #
    halfcld
    sincld
    #
    c2
    cc0
    wne
    #
    @12
    2ne0
    a1i
    @12
    @6
    @14
    wcel
    @6
    cc0
    wne
    @8
    cc0
    wne
    @17
    @12
    @6
    cc0
    @12
    @6
    cc0
    wceq
    #
    cc0
    cA
    wcel
    #
    @11
    @24
    @25
    wph
    @11
    @24
    wa
    cc0
    @6
    cA
    @24
    cc0
    @6
    wceq
    #
    @11
    @24
    @26
    @6
    cc0
    eqcom
    biimpi
    adantl
    @11
    @24
    simpl
    eqeltrd
    adantll
    wph
    @25
    wn
    @11
    @24
    fourierdlem58.0nA
    ad2antrr
    pm2.65da
    neqned
    @6
    fourierdlem44
    syl2anc
    mulne0d
    #
    redivcld
    fourierdlem58.k
    fmptd
    wph
    cA
    @14
    cr
    fourierdlem58.ass
    wph
    @13
    cpi
    wph
    cpi
    @15
    wph
    pire
    a1i
    #
    renegcld
    @28
    iccssred
    sstrd
    #
    cA
    cK
    dvfre
    syl2anc
    wph
    @3
    cA
    cr
    @0
    wph
    @0
    cA
    cc
    ccncf
    co
    #
    wcel
    #
    cA
    cc
    @0
    wf
    @3
    cA
    wceq
    wph
    @0
    cr
    vs
    cA
    @6
    cmpt
    #
    vs
    cA
    @9
    cmpt
    #
    cdiv
    cof
    co
    #
    cdv
    co
    @30
    wph
    cK
    @34
    cr
    cdv
    wph
    @34
    vs
    cA
    @10
    cmpt
    cK
    wph
    vs
    cA
    @6
    @9
    cdiv
    @32
    @33
    cioo
    crn
    ctg
    cfv
    #
    cr
    cr
    fourierdlem58.4
    @18
    @19
    wph
    @32
    eqidd
    wph
    @33
    eqidd
    offval2
    fourierdlem58.k
    syl6reqr
    oveq2d
    wph
    cr
    @32
    @33
    cA
    cr
    cr
    cc
    cpr
    wcel
    #
    wph
    reelprrecn
    a1i
    #
    wph
    vs
    cA
    @6
    cc
    @32
    @21
    @32
    eqid
    fmptd
    wph
    vs
    cA
    @9
    cc
    cc0
    csn
    #
    cdif
    #
    @33
    @12
    @9
    cc
    @38
    @12
    c2
    @8
    @20
    @22
    mulcld
    @12
    @9
    @38
    wcel
    #
    @9
    cc0
    wceq
    #
    @12
    @9
    cc0
    @27
    neneqd
    @12
    @9
    cr
    wcel
    @40
    @41
    wb
    @19
    @9
    cc0
    cr
    elsng
    syl
    mtbird
    eldifd
    @33
    eqid
    fmptd
    wph
    cr
    @32
    cdv
    co
    vs
    cA
    c1
    cmpt
    @30
    wph
    vs
    cA
    cr
    @37
    wph
    cA
    @35
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    fourierdlem58.4
    @42
    @42
    eqid
    #
    tgioo2
    #
    syl6eleq
    dvmptidg
    wph
    vs
    cA
    c1
    cc
    wph
    cA
    cr
    cc
    @29
    cr
    cc
    wss
    #
    wph
    ax-resscn
    a1i
    #
    sstrd
    #
    wph
    1cnd
    cc
    cc
    wss
    #
    wph
    cc
    ssid
    #
    a1i
    #
    constcncfg
    eqeltrd
    wph
    cr
    @33
    cdv
    co
    #
    vs
    cA
    @7
    ccos
    cfv
    #
    cmpt
    #
    @30
    wph
    @51
    cr
    vs
    cr
    @9
    cmpt
    #
    cA
    cres
    #
    cdv
    co
    #
    cr
    @54
    cdv
    co
    #
    cA
    @35
    cnt
    cfv
    cfv
    #
    cres
    #
    @53
    wph
    @33
    @55
    cr
    cdv
    wph
    @55
    @33
    wph
    vs
    cr
    cA
    @9
    @29
    resmptd
    eqcomd
    oveq2d
    wph
    @45
    cr
    cc
    @54
    wf
    #
    cr
    cr
    wss
    #
    @5
    @56
    @59
    wceq
    @46
    @60
    wph
    vs
    cr
    cc
    @9
    @54
    @54
    eqid
    @6
    cr
    wcel
    #
    c2
    @8
    @62
    2cnd
    @62
    @7
    @62
    @6
    @6
    recn
    #
    halfcld
    sincld
    mulcld
    fmpti
    a1i
    @61
    wph
    cr
    ssid
    a1i
    @29
    cr
    cA
    cr
    @35
    @54
    @42
    @43
    @44
    dvres
    syl22anc
    wph
    @59
    @57
    cA
    cres
    #
    vs
    cc
    @52
    cmpt
    #
    cr
    cres
    #
    cA
    cres
    #
    @53
    wph
    @58
    cA
    @57
    wph
    cA
    @35
    wcel
    #
    @58
    cA
    wceq
    #
    fourierdlem58.4
    wph
    @35
    ctop
    wcel
    #
    @5
    @68
    @69
    wb
    @70
    wph
    retop
    a1i
    @29
    cA
    @35
    cr
    uniretop
    isopn3
    syl2anc
    mpbid
    reseq2d
    @64
    @67
    wceq
    wph
    @57
    @66
    cA
    @57
    cr
    vs
    cc
    c2
    c1
    c2
    cdiv
    co
    #
    @6
    cmul
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cr
    cres
    #
    cdv
    co
    #
    cc
    @75
    cdv
    co
    #
    cr
    cres
    #
    @66
    @54
    @76
    cr
    cdv
    @76
    vs
    cr
    @74
    cmpt
    #
    @54
    @45
    @76
    @80
    wceq
    ax-resscn
    vs
    cc
    cr
    @74
    resmpt
    ax-mp
    vs
    cr
    @74
    @9
    @62
    @73
    @8
    c2
    cmul
    @62
    @72
    @7
    csin
    @62
    @6
    cc
    wcel
    #
    @72
    @7
    wceq
    @63
    @81
    @7
    @72
    @81
    @6
    c2
    @81
    id
    #
    @81
    2cnd
    #
    @23
    @81
    2ne0
    a1i
    divrec2d
    eqcomd
    #
    syl
    fveq2d
    oveq2d
    mpteq2ia
    eqtr2i
    oveq2i
    @36
    cc
    cc
    @75
    wf
    @48
    cr
    @78
    cdm
    #
    wss
    @77
    @79
    wceq
    reelprrecn
    vs
    cc
    cc
    @74
    @75
    @75
    eqid
    @81
    c2
    @73
    @83
    @81
    @72
    @81
    @71
    @6
    @71
    cc
    wcel
    #
    @81
    halfcn
    a1i
    @82
    mulcld
    sincld
    mulcld
    fmpti
    @49
    cr
    cc
    @85
    ax-resscn
    @85
    @65
    cdm
    #
    cc
    @78
    @65
    @78
    vs
    cc
    c2
    @71
    cmul
    co
    #
    @72
    ccos
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    @65
    c2
    cc
    wcel
    #
    @86
    @78
    @91
    wceq
    2cn
    halfcn
    vs
    c2
    @71
    dvasinbx
    mp2an
    vs
    cc
    @90
    @52
    @81
    @90
    c1
    @52
    cmul
    co
    @52
    @81
    @88
    c1
    @89
    @52
    cmul
    @88
    c1
    wceq
    @81
    c2
    2cn
    2ne0
    recidi
    a1i
    @81
    @72
    @7
    ccos
    @84
    fveq2d
    oveq12d
    @81
    @52
    @81
    @7
    @6
    halfcl
    coscld
    #
    mulid2d
    eqtrd
    mpteq2ia
    eqtri
    #
    dmeqi
    @52
    cc
    wcel
    @87
    cc
    wceq
    vs
    cc
    vs
    cc
    @52
    cc
    dmmptg
    @93
    mprg
    eqtri
    sseqtr4i
    cc
    cr
    @75
    dvres3
    mp4an
    @78
    @65
    cr
    @94
    reseq1i
    3eqtri
    reseq1i
    a1i
    wph
    @67
    @65
    cA
    cres
    @53
    wph
    @65
    cA
    cr
    @29
    resabs1d
    wph
    vs
    cc
    cA
    @52
    @47
    resmptd
    eqtrd
    3eqtrd
    3eqtrd
    wph
    vs
    @7
    ccos
    cA
    ccos
    cc
    cc
    ccncf
    co
    wcel
    wph
    coscn
    a1i
    wph
    vs
    @6
    c2
    cA
    wph
    vs
    cA
    cc
    @47
    @50
    idcncfg
    wph
    vs
    cA
    c2
    @39
    @47
    wph
    @92
    @23
    c2
    @39
    wcel
    wph
    2cnd
    @23
    wph
    2ne0
    a1i
    c2
    cc
    cc0
    eldifsn
    sylanbrc
    wph
    cc
    @38
    difssd
    constcncfg
    divcncf
    cncfmpt1f
    eqeltrd
    dvdivcncf
    eqeltrd
    #
    cA
    cc
    @0
    cncff
    cA
    cc
    @0
    fdm
    3syl
    feq2d
    mpbid
    wph
    @45
    @31
    @1
    @2
    wb
    @46
    @95
    cA
    cc
    cr
    @0
    cncffvrn
    syl2anc
    mpbird
end
