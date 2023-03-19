include "cr.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "eqid.mm"
include "tgioo2.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "reelprrecn.mm"
include "a1i.mm"
include "cnt.mm"
include "wceq.mm"
include "ctop.mm"
include "wss.mm"
include "retop.mm"
include "wf1o.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "ccncf.mm"
include "co.mm"
include "wf.mm"
include "cncff.mm"
include "frn.mm"
include "eqsstr3d.mm"
include "uniretop.mm"
include "ntrss2.mm"
include "sylancr.mm"
include "cv.mm"
include "wa.mm"
include "ccnv.mm"
include "f1ocnvfv2.mm"
include "sylan.mm"
include "crest.mm"
include "ccnp.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "cbl.mm"
include "crp.mm"
include "wrex.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "ffvelrnda.mm"
include "cdv.mm"
include "cdm.mm"
include "dvbsss.mm"
include "ax-resscn.mm"
include "syl.mm"
include "fss.mm"
include "sylancl.mm"
include "dvbssntr.mm"
include "eqssd.mm"
include "wb.mm"
include "isopn3.mm"
include "mpbird.mm"
include "cxmt.mm"
include "rexmet.mm"
include "cmopn.mm"
include "tgioo.mm"
include "mopni2.mm"
include "mp3an1.mm"
include "syldan.mm"
include "c2.mm"
include "cdiv.mm"
include "ad2antrr.mm"
include "cc0.mm"
include "wn.mm"
include "adantr.mm"
include "rphalfcl.mm"
include "ad2antrl.mm"
include "caddc.mm"
include "cicc.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "w3a.mm"
include "sseldd.mm"
include "rpred.mm"
include "resubcld.mm"
include "readdcld.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "simp1d.mm"
include "simplrl.mm"
include "rphalflt.mm"
include "ltsub2dd.mm"
include "simp2d.mm"
include "ltletrd.mm"
include "simp3d.mm"
include "ltadd2dd.mm"
include "lelttrd.mm"
include "cxr.mm"
include "rexrd.mm"
include "elioo2.mm"
include "mpbir3and.mm"
include "ex.mm"
include "ssrdv.mm"
include "rpre.mm"
include "bl2ioo.mm"
include "sseqtr4d.mm"
include "simprr.mm"
include "sstrd.mm"
include "dvcnvrelem2.mm"
include "rexlimddv.mm"
include "simpld.mm"
include "eqeltrrd.mm"
include "ccn.mm"
include "wral.mm"
include "simprd.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "ralrimiva.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "syl6ss.mm"
include "resttopon.mm"
include "cncnp.mm"
include "mpbir2and.mm"
include "cncfcn.mm"
include "eleqtrrd.mm"
include "dvcnv.mm"

theorem dvcnvre
  let wph: wff ph
  let vx: setvar x
  let cF: class F
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let cC: class C
  let vr: setvar r
  let cR: class R
  assume dvcnvre.f: |- ( ph -> F e. ( X -cn-> RR ) )
  assume dvcnvre.d: |- ( ph -> dom ( RR _D F ) = X )
  assume dvcnvre.z: |- ( ph -> -. 0 e. ran ( RR _D F ) )
  assume dvcnvre.1: |- ( ph -> F : X -1-1-onto-> Y )

  disjoint F x
  disjoint ph x
  disjoint X x
  disjoint Y x
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint r x
  disjoint r y
  disjoint F r
  disjoint F y
  disjoint ph r
  disjoint ph y
  disjoint X r
  disjoint X y
  disjoint Y r
  disjoint Y y
  disjoint R x
  disjoint R y
  assert |- ( ph -> ( RR _D `' F ) = ( x e. Y |-> ( 1 / ( ( RR _D F ) ` ( `' F ` x ) ) ) ) )

  proof
    wph
    vx
    cr
    cF
    ccnfld
    ctopn
    cfv
    #
    cioo
    crn
    ctg
    cfv
    #
    cX
    cY
    @0
    eqid
    #
    @0
    @2
    tgioo2
    #
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    wph
    cY
    @1
    wcel
    #
    cY
    @1
    cnt
    cfv
    #
    cfv
    #
    cY
    wceq
    #
    wph
    @6
    cY
    wph
    @1
    ctop
    wcel
    #
    cY
    cr
    wss
    #
    @6
    cY
    wss
    retop
    wph
    cY
    cF
    crn
    #
    cr
    wph
    cX
    cY
    cF
    wf1o
    #
    cX
    cY
    cF
    wfo
    @10
    cY
    wceq
    dvcnvre.1
    cX
    cY
    cF
    f1ofo
    cX
    cY
    cF
    forn
    3syl
    wph
    cF
    cX
    cr
    ccncf
    co
    wcel
    #
    cX
    cr
    cF
    wf
    #
    @10
    cr
    wss
    dvcnvre.f
    cX
    cr
    cF
    cncff
    #
    cX
    cr
    cF
    frn
    3syl
    eqsstr3d
    #
    cY
    @1
    cr
    uniretop
    ntrss2
    sylancr
    wph
    vx
    cY
    @6
    wph
    vx
    cv
    #
    cY
    wcel
    #
    @16
    @6
    wcel
    wph
    @17
    wa
    #
    @16
    cF
    ccnv
    #
    cfv
    #
    cF
    cfv
    #
    @16
    @6
    wph
    @11
    @17
    @21
    @16
    wceq
    dvcnvre.1
    cX
    cY
    @16
    cF
    f1ocnvfv2
    sylan
    #
    @18
    @21
    @6
    wcel
    #
    @19
    @21
    @0
    cY
    crest
    co
    #
    @0
    cX
    crest
    co
    #
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    @18
    @20
    vr
    cv
    #
    cabs
    cmin
    ccom
    cr
    cr
    cxp
    cres
    #
    cbl
    cfv
    co
    #
    cX
    wss
    #
    @23
    @28
    wa
    vr
    crp
    wph
    @17
    @20
    cX
    wcel
    #
    @32
    vr
    crp
    wrex
    #
    wph
    cY
    cX
    @16
    @19
    wph
    @11
    cY
    cX
    @19
    wf1o
    cY
    cX
    @19
    wf
    #
    dvcnvre.1
    cX
    cY
    cF
    f1ocnv
    cY
    cX
    @19
    f1of
    3syl
    #
    ffvelrnda
    #
    wph
    cX
    @1
    wcel
    #
    @33
    @34
    wph
    @38
    cX
    @5
    cfv
    #
    cX
    wceq
    #
    wph
    @39
    cX
    wph
    @8
    cX
    cr
    wss
    #
    @39
    cX
    wss
    retop
    wph
    cX
    cr
    cF
    cdv
    co
    #
    cdm
    #
    cr
    dvcnvre.d
    @43
    cr
    wss
    wph
    cr
    cF
    dvbsss
    a1i
    eqsstr3d
    #
    cX
    @1
    cr
    uniretop
    ntrss2
    sylancr
    wph
    cX
    @43
    @39
    dvcnvre.d
    wph
    cX
    cr
    cF
    @1
    @0
    cr
    cc
    wss
    #
    wph
    ax-resscn
    a1i
    wph
    @13
    @45
    cX
    cc
    cF
    wf
    wph
    @12
    @13
    dvcnvre.f
    @14
    syl
    ax-resscn
    cX
    cr
    cc
    cF
    fss
    sylancl
    @44
    @3
    @2
    dvbssntr
    eqsstr3d
    eqssd
    wph
    @8
    @41
    @38
    @40
    wb
    retop
    @44
    cX
    @1
    cr
    uniretop
    isopn3
    sylancr
    mpbird
    @30
    cr
    cxmt
    cfv
    wcel
    @38
    @33
    @34
    @30
    @30
    eqid
    #
    rexmet
    vr
    cX
    @30
    @20
    @1
    cr
    @30
    @30
    cmopn
    cfv
    #
    @46
    @47
    eqid
    tgioo
    mopni2
    mp3an1
    sylan
    syldan
    @18
    @29
    crp
    wcel
    #
    @32
    wa
    #
    wa
    #
    @20
    @29
    c2
    cdiv
    co
    #
    @1
    cF
    @0
    @25
    @24
    cX
    cY
    wph
    @12
    @17
    @49
    dvcnvre.f
    ad2antrr
    wph
    @43
    cX
    wceq
    @17
    @49
    dvcnvre.d
    ad2antrr
    wph
    cc0
    @42
    crn
    wcel
    wn
    @17
    @49
    dvcnvre.z
    ad2antrr
    wph
    @11
    @17
    @49
    dvcnvre.1
    ad2antrr
    @18
    @33
    @49
    @37
    adantr
    #
    @48
    @51
    crp
    wcel
    #
    @18
    @32
    @29
    rphalfcl
    #
    ad2antrl
    #
    @50
    @20
    @51
    cmin
    co
    #
    @20
    @51
    caddc
    co
    #
    cicc
    co
    #
    @31
    cX
    @50
    @58
    @20
    @29
    cmin
    co
    #
    @20
    @29
    caddc
    co
    #
    cioo
    co
    #
    @31
    @50
    vy
    @58
    @61
    @50
    vy
    cv
    #
    @58
    wcel
    #
    @62
    @61
    wcel
    #
    @50
    @63
    wa
    #
    @64
    @62
    cr
    wcel
    #
    @59
    @62
    clt
    wbr
    #
    @62
    @60
    clt
    wbr
    #
    @65
    @66
    @56
    @62
    cle
    wbr
    #
    @62
    @57
    cle
    wbr
    #
    @50
    @63
    @66
    @69
    @70
    w3a
    #
    @50
    @56
    cr
    wcel
    #
    @57
    cr
    wcel
    #
    @63
    @71
    wb
    @50
    @20
    @51
    @50
    cX
    cr
    @20
    wph
    @41
    @17
    @49
    @44
    ad2antrr
    @52
    sseldd
    #
    @50
    @51
    @55
    rpred
    #
    resubcld
    #
    @50
    @20
    @51
    @74
    @75
    readdcld
    #
    @56
    @57
    @62
    elicc2
    syl2anc
    biimpa
    #
    simp1d
    #
    @65
    @59
    @56
    @62
    @65
    @20
    @29
    @50
    @20
    cr
    wcel
    #
    @63
    @74
    adantr
    #
    @65
    @29
    @18
    @48
    @32
    @63
    simplrl
    #
    rpred
    #
    resubcld
    #
    @50
    @72
    @63
    @76
    adantr
    @79
    @65
    @51
    @29
    @20
    @65
    @51
    @65
    @48
    @53
    @82
    @54
    syl
    rpred
    #
    @83
    @81
    @65
    @48
    @51
    @29
    clt
    wbr
    @82
    @29
    rphalflt
    syl
    #
    ltsub2dd
    @65
    @66
    @69
    @70
    @78
    simp2d
    ltletrd
    @65
    @62
    @57
    @60
    @79
    @50
    @73
    @63
    @77
    adantr
    @65
    @20
    @29
    @81
    @83
    readdcld
    #
    @65
    @66
    @69
    @70
    @78
    simp3d
    @65
    @51
    @29
    @20
    @85
    @83
    @81
    @86
    ltadd2dd
    lelttrd
    @65
    @59
    cxr
    wcel
    @60
    cxr
    wcel
    @64
    @66
    @67
    @68
    w3a
    wb
    @65
    @59
    @84
    rexrd
    @65
    @60
    @87
    rexrd
    @59
    @60
    @62
    elioo2
    syl2anc
    mpbir3and
    ex
    ssrdv
    @50
    @80
    @29
    cr
    wcel
    #
    @31
    @61
    wceq
    @74
    @48
    @88
    @18
    @32
    @29
    rpre
    ad2antrl
    @20
    @29
    @30
    @46
    bl2ioo
    syl2anc
    sseqtr4d
    @18
    @48
    @32
    simprr
    sstrd
    @1
    eqid
    @2
    @25
    eqid
    #
    @24
    eqid
    #
    dvcnvrelem2
    rexlimddv
    #
    simpld
    eqeltrrd
    ex
    ssrdv
    eqssd
    wph
    @8
    @9
    @4
    @7
    wb
    retop
    @15
    cY
    @1
    cr
    uniretop
    isopn3
    sylancr
    mpbird
    dvcnvre.1
    wph
    @19
    @24
    @25
    ccn
    co
    #
    cY
    cX
    ccncf
    co
    #
    wph
    @19
    @92
    wcel
    #
    @35
    @19
    @16
    @26
    cfv
    #
    wcel
    #
    vx
    cY
    wral
    #
    @36
    wph
    @96
    vx
    cY
    @18
    @19
    @27
    @95
    @18
    @23
    @28
    @91
    simprd
    @18
    @21
    @16
    @26
    @22
    fveq2d
    eleqtrd
    ralrimiva
    wph
    @24
    cY
    ctopon
    cfv
    wcel
    #
    @25
    cX
    ctopon
    cfv
    wcel
    #
    @94
    @35
    @97
    wa
    wb
    wph
    @0
    cc
    ctopon
    cfv
    wcel
    #
    cY
    cc
    wss
    #
    @98
    @0
    @2
    cnfldtopon
    #
    wph
    cY
    cr
    cc
    @15
    ax-resscn
    syl6ss
    #
    cY
    @0
    cc
    resttopon
    sylancr
    wph
    @100
    cX
    cc
    wss
    #
    @99
    @102
    wph
    cX
    cr
    cc
    @44
    ax-resscn
    syl6ss
    #
    cX
    @0
    cc
    resttopon
    sylancr
    vx
    @19
    @24
    @25
    cY
    cX
    cncnp
    syl2anc
    mpbir2and
    wph
    @101
    @104
    @93
    @92
    wceq
    @103
    @105
    cY
    cX
    @0
    @24
    @25
    @2
    @90
    @89
    cncfcn
    syl2anc
    eleqtrrd
    dvcnvre.d
    dvcnvre.z
    dvcnv
end
