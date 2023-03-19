include "cms.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "cres.mm"
include "ccld.mm"
include "wa.mm"
include "ccl.mm"
include "wss.mm"
include "cv.mm"
include "cflim.mm"
include "co.mm"
include "cfil.mm"
include "wrex.mm"
include "ctopon.mm"
include "wb.mm"
include "cxmt.mm"
include "cme.mm"
include "cmetmet.mm"
include "metxmet.mm"
include "syl.mm"
include "adantr.mm"
include "mopntopon.mm"
include "cdm.mm"
include "resss.mm"
include "dmss.mm"
include "mp2b.mm"
include "wceq.mm"
include "metdmdm.mm"
include "sseq12.mm"
include "syl2anr.mm"
include "mpbiri.mm"
include "flimcls.mm"
include "syl2anc.mm"
include "simprrr.mm"
include "wmo.mm"
include "wex.mm"
include "wi.mm"
include "cha.mm"
include "methaus.mm"
include "hausflimi.mm"
include "3syl.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cmopn.mm"
include "crest.mm"
include "simprl.mm"
include "simprrl.mm"
include "flimrest.mm"
include "syl3anc.mm"
include "eqid.mm"
include "metrest.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "ccfil.mm"
include "simplr.mm"
include "flimcfil.mm"
include "cfilres.mm"
include "mpbid.mm"
include "cmetcvg.mm"
include "eqnetrd.mm"
include "n0.mm"
include "elin.mm"
include "exbii.mm"
include "bitri.mm"
include "sylib.mm"
include "mopick.mm"
include "mpd.mm"
include "rexlimdvaa.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "ctop.mm"
include "cuni.mm"
include "mopntop.mm"
include "mopnuni.mm"
include "sseqtrd.mm"
include "iscld4.mm"
include "mpbird.mm"
include "wral.mm"
include "cldss.mm"
include "adantl.mm"
include "sseqtr4d.mm"
include "metres2.mm"
include "cfg.mm"
include "ad2antrr.mm"
include "eqcomd.mm"
include "cfilfil.mm"
include "sylan.mm"
include "elfvdm.mm"
include "trfg.mm"
include "oveq12d.mm"
include "cfbas.mm"
include "cpw.mm"
include "filfbas.mm"
include "filsspw.mm"
include "sspwb.mm"
include "sstrd.mm"
include "fbasweak.mm"
include "fgcl.mm"
include "ssfg.mm"
include "filtop.mm"
include "sseldd.mm"
include "flimclsi.mm"
include "cldcls.mm"
include "ad2antlr.mm"
include "df-ss.mm"
include "3eqtrd.mm"
include "simpll.mm"
include "cfilresi.mm"
include "ralrimiva.mm"
include "iscmet.mm"
include "sylanbrc.mm"
include "impbida.mm"

theorem cmetss
  let cD: class D
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vx: setvar x
  assume cmetss.2: |- J = ( MetOpen ` D )


  assert |- ( D e. ( CMet ` X ) -> ( ( D |` ( Y X. Y ) ) e. ( CMet ` Y ) <-> Y e. ( Clsd ` J ) ) )

  proof
    cD
    cX
    cms
    cfv
    wcel
    #
    cD
    cY
    cY
    cxp
    #
    cres
    #
    cY
    cms
    cfv
    wcel
    #
    cY
    cJ
    ccld
    cfv
    wcel
    #
    @0
    @3
    wa
    #
    @4
    cY
    cJ
    ccl
    cfv
    cfv
    #
    cY
    wss
    #
    @5
    vx
    @6
    cY
    @5
    vx
    cv
    #
    @6
    wcel
    #
    cY
    vf
    cv
    #
    wcel
    #
    @8
    cJ
    @10
    cflim
    co
    #
    wcel
    #
    wa
    #
    vf
    cX
    cfil
    cfv
    #
    wrex
    #
    @8
    cY
    wcel
    #
    @5
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cY
    cX
    wss
    #
    @9
    @16
    wb
    @5
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @18
    @0
    @20
    @3
    @0
    cD
    cX
    cme
    cfv
    wcel
    #
    @20
    cD
    cX
    cmetmet
    #
    cD
    cX
    metxmet
    #
    syl
    #
    adantr
    #
    cD
    cJ
    cX
    cmetss.2
    mopntopon
    #
    syl
    @5
    @19
    @2
    cdm
    #
    cdm
    #
    cD
    cdm
    #
    cdm
    #
    wss
    #
    @2
    cD
    wss
    @27
    @29
    wss
    @31
    cD
    @1
    resss
    @2
    cD
    dmss
    @27
    @29
    dmss
    mp2b
    @3
    cY
    @28
    wceq
    #
    cX
    @30
    wceq
    #
    @19
    @31
    wb
    @0
    @3
    @2
    cY
    cme
    cfv
    wcel
    #
    @32
    @2
    cY
    cmetmet
    @2
    cY
    metdmdm
    syl
    @0
    @21
    @33
    @22
    cD
    cX
    metdmdm
    syl
    cY
    @28
    cX
    @30
    sseq12
    syl2anr
    mpbiri
    #
    @8
    cY
    vf
    cJ
    cX
    flimcls
    syl2anc
    @5
    @14
    @17
    vf
    @15
    @5
    @10
    @15
    wcel
    #
    @14
    wa
    #
    wa
    #
    @13
    @17
    @5
    @36
    @11
    @13
    simprrr
    #
    @38
    @13
    vx
    wmo
    #
    @13
    @17
    wa
    #
    vx
    wex
    #
    @13
    @17
    wi
    @38
    @20
    cJ
    cha
    wcel
    @40
    @5
    @20
    @37
    @25
    adantr
    #
    cD
    cJ
    cX
    cmetss.2
    methaus
    vx
    @10
    cJ
    hausflimi
    3syl
    @38
    @12
    cY
    cin
    #
    c0
    wne
    #
    @42
    @38
    @44
    @2
    cmopn
    cfv
    #
    @10
    cY
    crest
    co
    #
    cflim
    co
    #
    c0
    @38
    cJ
    cY
    crest
    co
    #
    @47
    cflim
    co
    #
    @44
    @48
    @38
    @18
    @36
    @11
    @50
    @44
    wceq
    @38
    @20
    @18
    @43
    @26
    syl
    @5
    @36
    @14
    simprl
    #
    @5
    @36
    @11
    @13
    simprrl
    #
    @10
    cJ
    cX
    cY
    flimrest
    syl3anc
    @38
    @49
    @46
    @47
    cflim
    @38
    @20
    @19
    @49
    @46
    wceq
    #
    @43
    @5
    @19
    @37
    @35
    adantr
    cD
    @2
    cJ
    @46
    cX
    cY
    @2
    eqid
    cmetss.2
    @46
    eqid
    #
    metrest
    #
    syl2anc
    oveq1d
    eqtr3d
    @38
    @3
    @47
    @2
    ccfil
    cfv
    #
    wcel
    #
    @48
    c0
    wne
    @0
    @3
    @37
    simplr
    @38
    @10
    cD
    ccfil
    cfv
    #
    wcel
    #
    @57
    @38
    @20
    @13
    @59
    @43
    @39
    @8
    cD
    @10
    cJ
    cX
    cmetss.2
    flimcfil
    syl2anc
    @38
    @20
    @36
    @11
    @59
    @57
    wb
    @43
    @51
    @52
    cD
    @10
    cX
    cY
    cfilres
    syl3anc
    mpbid
    @2
    @47
    @46
    cY
    @54
    cmetcvg
    syl2anc
    eqnetrd
    @45
    @8
    @44
    wcel
    #
    vx
    wex
    @42
    vx
    @44
    n0
    @60
    @41
    vx
    @8
    @12
    cY
    elin
    exbii
    bitri
    sylib
    @13
    @17
    vx
    mopick
    syl2anc
    mpd
    rexlimdvaa
    sylbid
    ssrdv
    @5
    cJ
    ctop
    wcel
    #
    cY
    cJ
    cuni
    #
    wss
    #
    @4
    @7
    wb
    @5
    @20
    @61
    @25
    cD
    cJ
    cX
    cmetss.2
    mopntop
    syl
    @5
    cY
    cX
    @62
    @35
    @5
    @20
    cX
    @62
    wceq
    #
    @25
    cD
    cJ
    cX
    cmetss.2
    mopnuni
    #
    syl
    sseqtrd
    cY
    cJ
    @62
    @62
    eqid
    #
    iscld4
    syl2anc
    mpbird
    @0
    @4
    wa
    #
    @34
    @46
    @10
    cflim
    co
    #
    c0
    wne
    #
    vf
    @56
    wral
    @3
    @67
    @21
    @19
    @34
    @0
    @21
    @4
    @22
    adantr
    #
    @67
    cY
    @62
    cX
    @4
    @63
    @0
    cY
    cJ
    @62
    @66
    cldss
    adantl
    @67
    @21
    @20
    @64
    @70
    @23
    @65
    3syl
    sseqtr4d
    #
    cD
    cY
    cX
    metres2
    syl2anc
    #
    @67
    @69
    vf
    @56
    @67
    @10
    @56
    wcel
    #
    wa
    #
    @68
    cJ
    cX
    @10
    cfg
    co
    #
    cflim
    co
    #
    c0
    @74
    @68
    @49
    @75
    cY
    crest
    co
    #
    cflim
    co
    #
    @76
    cY
    cin
    #
    @76
    @74
    @46
    @49
    @10
    @77
    cflim
    @74
    @49
    @46
    @74
    @20
    @19
    @53
    @0
    @20
    @4
    @73
    @24
    ad2antrr
    #
    @67
    @19
    @73
    @71
    adantr
    #
    @55
    syl2anc
    eqcomd
    @74
    @77
    @10
    @74
    @10
    cY
    cfil
    cfv
    wcel
    #
    @19
    cX
    cms
    cdm
    #
    wcel
    #
    @77
    @10
    wceq
    @67
    @2
    cY
    cxmt
    cfv
    wcel
    #
    @73
    @82
    @67
    @34
    @85
    @72
    @2
    cY
    metxmet
    syl
    @2
    @10
    cY
    cfilfil
    sylan
    #
    @81
    @0
    @84
    @4
    @73
    cD
    cX
    cms
    elfvdm
    ad2antrr
    #
    cY
    @10
    @83
    cX
    trfg
    syl3anc
    eqcomd
    oveq12d
    @74
    @18
    @75
    @15
    wcel
    #
    cY
    @75
    wcel
    #
    @78
    @79
    wceq
    @74
    @20
    @18
    @80
    @26
    syl
    @74
    @10
    cX
    cfbas
    cfv
    wcel
    #
    @88
    @74
    @10
    cY
    cfbas
    cfv
    wcel
    #
    @10
    cX
    cpw
    #
    wss
    @84
    @90
    @74
    @82
    @91
    @86
    @10
    cY
    filfbas
    syl
    @74
    @10
    cY
    cpw
    #
    @92
    @74
    @82
    @10
    @93
    wss
    @86
    @10
    cY
    filsspw
    syl
    @74
    @19
    @93
    @92
    wss
    @81
    cY
    cX
    sspwb
    sylib
    sstrd
    @87
    @10
    @83
    cY
    cX
    fbasweak
    syl3anc
    #
    @10
    cX
    fgcl
    syl
    @74
    @10
    @75
    cY
    @74
    @90
    @10
    @75
    wss
    @94
    @10
    cX
    ssfg
    syl
    @74
    @82
    @11
    @86
    @10
    cY
    filtop
    syl
    sseldd
    #
    @75
    cJ
    cX
    cY
    flimrest
    syl3anc
    @74
    @76
    cY
    wss
    @79
    @76
    wceq
    @74
    @76
    @6
    cY
    @74
    @89
    @76
    @6
    wss
    @95
    cY
    @75
    cJ
    flimclsi
    syl
    @4
    @6
    cY
    wceq
    @0
    @73
    cY
    cJ
    cldcls
    ad2antlr
    sseqtrd
    @76
    cY
    df-ss
    sylib
    3eqtrd
    @74
    @0
    @75
    @58
    wcel
    #
    @76
    c0
    wne
    @0
    @4
    @73
    simpll
    @67
    @20
    @73
    @96
    @67
    @21
    @20
    @70
    @23
    syl
    cD
    @10
    cX
    cY
    cfilresi
    sylan
    cD
    @75
    cJ
    cX
    cmetss.2
    cmetcvg
    syl2anc
    eqnetrd
    ralrimiva
    @2
    vf
    @46
    cY
    @54
    iscmet
    sylanbrc
    impbida
end
