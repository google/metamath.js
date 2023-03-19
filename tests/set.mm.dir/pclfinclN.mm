include "cfn.mm"
include "wcel.mm"
include "chlt.mm"
include "wss.mm"
include "cfv.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "sseq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "pcl0N.mm"
include "0psubclN.mm"
include "eqeltrd.mm"
include "adantr.mm"
include "anass.mm"
include "vex.mm"
include "snss.mm"
include "anbi2i.mm"
include "unss.mm"
include "bitri.mm"
include "bitr2i.mm"
include "simpllr.mm"
include "uneq1d.mm"
include "uncom.mm"
include "un0.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "cpsubsp.mm"
include "simplrl.mm"
include "cal.mm"
include "hlatl.mm"
include "syl.mm"
include "simprr.mm"
include "eqid.mm"
include "snatpsubN.mm"
include "syl2anc.mm"
include "pclidN.mm"
include "eqtrd.mm"
include "atpsubclN.mm"
include "exp43.mm"
include "wne.mm"
include "cpadd.mm"
include "co.mm"
include "pclssidN.mm"
include "ad2antlr.mm"
include "unss1.mm"
include "simprl.mm"
include "psubclssatN.mm"
include "snssi.mm"
include "ad2antll.mm"
include "paddunssN.mm"
include "syl3anc.mm"
include "sstrd.mm"
include "paddssat.mm"
include "pclssN.mm"
include "paddatclN.mm"
include "psubclsubN.mm"
include "sseqtrd.mm"
include "wel.mm"
include "wral.mm"
include "cjn.mm"
include "cple.mm"
include "wbr.mm"
include "wrex.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "pcl0bN.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "elpaddat.mm"
include "syl31anc.mm"
include "w3a.mm"
include "simp1rl.mm"
include "3ad2ant1.mm"
include "simpl13.mm"
include "simpl.mm"
include "sylbir.mm"
include "simpl2.mm"
include "elpcliN.mm"
include "biimpri.mm"
include "adantl.mm"
include "simpl3.mm"
include "psubspi2N.mm"
include "syl33anc.mm"
include "exp520.mm"
include "rexlimdv.mm"
include "3expia.mm"
include "impd.mm"
include "sylbid.mm"
include "ralrimdv.mm"
include "simplrr.mm"
include "jca.mm"
include "sylib.mm"
include "elpclN.mm"
include "sylibrd.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "pm2.61dane.mm"
include "a2d.mm"
include "imp4b.mm"
include "syl5bi.mm"
include "ex.mm"
include "findcard2.mm"
include "3impib.mm"
include "3coml.mm"

theorem pclfinclN
  let cA: class A
  let cS: class S
  let cU: class U
  let cK: class K
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pclfincl.a: |- A = ( Atoms ` K )
  assume pclfincl.c: |- U = ( PCl ` K )
  assume pclfincl.s: |- S = ( PSubCl ` K )


  assert |- ( ( K e. HL /\ X C_ A /\ X e. Fin ) -> ( U ` X ) e. S )

  proof
    cX
    cfn
    wcel
    #
    cK
    chlt
    wcel
    #
    cX
    cA
    wss
    #
    cX
    cU
    cfv
    #
    cS
    wcel
    #
    @0
    @1
    @2
    @4
    @1
    vx
    cv
    #
    cA
    wss
    #
    wa
    #
    @5
    cU
    cfv
    #
    cS
    wcel
    #
    wi
    @1
    c0
    cA
    wss
    #
    wa
    #
    c0
    cU
    cfv
    #
    cS
    wcel
    #
    wi
    @1
    vy
    cv
    #
    cA
    wss
    #
    wa
    #
    @14
    cU
    cfv
    #
    cS
    wcel
    #
    wi
    #
    @1
    @14
    vz
    cv
    #
    csn
    #
    cun
    #
    cA
    wss
    #
    wa
    #
    @22
    cU
    cfv
    #
    cS
    wcel
    #
    wi
    #
    @1
    @2
    wa
    #
    @4
    wi
    vx
    vy
    vz
    cX
    @5
    c0
    wceq
    #
    @7
    @11
    @9
    @13
    @29
    @6
    @10
    @1
    @5
    c0
    cA
    sseq1
    anbi2d
    @29
    @8
    @12
    cS
    @5
    c0
    cU
    fveq2
    eleq1d
    imbi12d
    @5
    @14
    wceq
    #
    @7
    @16
    @9
    @18
    @30
    @6
    @15
    @1
    @5
    @14
    cA
    sseq1
    anbi2d
    @30
    @8
    @17
    cS
    @5
    @14
    cU
    fveq2
    eleq1d
    imbi12d
    @5
    @22
    wceq
    #
    @7
    @24
    @9
    @26
    @31
    @6
    @23
    @1
    @5
    @22
    cA
    sseq1
    anbi2d
    @31
    @8
    @25
    cS
    @5
    @22
    cU
    fveq2
    eleq1d
    imbi12d
    @5
    cX
    wceq
    #
    @7
    @28
    @9
    @4
    @32
    @6
    @2
    @1
    @5
    cX
    cA
    sseq1
    anbi2d
    @32
    @8
    @3
    cS
    @5
    cX
    cU
    fveq2
    eleq1d
    imbi12d
    @1
    @13
    @10
    @1
    @12
    c0
    cS
    cU
    cK
    pclfincl.c
    pcl0N
    cS
    cK
    pclfincl.s
    0psubclN
    eqeltrd
    adantr
    @14
    cfn
    wcel
    #
    @19
    @27
    @24
    @16
    @20
    cA
    wcel
    #
    wa
    #
    @33
    @19
    wa
    @26
    @35
    @1
    @15
    @34
    wa
    #
    wa
    @24
    @1
    @15
    @34
    anass
    @36
    @23
    @1
    @36
    @15
    @21
    cA
    wss
    #
    wa
    @23
    @34
    @37
    @15
    @20
    cA
    vz
    vex
    #
    snss
    anbi2i
    @14
    @21
    cA
    unss
    bitri
    #
    anbi2i
    bitr2i
    @33
    @19
    @16
    @34
    @26
    @33
    @16
    @18
    @34
    @26
    wi
    #
    @33
    @16
    @18
    @40
    wi
    wi
    @14
    c0
    @33
    @14
    c0
    wceq
    #
    wa
    #
    @16
    @18
    @34
    @26
    @42
    @16
    wa
    #
    @18
    @34
    wa
    #
    wa
    #
    @25
    @21
    cS
    @45
    @25
    @21
    cU
    cfv
    #
    @21
    @45
    @22
    @21
    cU
    @45
    @22
    c0
    @21
    cun
    #
    @21
    @45
    @14
    c0
    @21
    @33
    @41
    @16
    @44
    simpllr
    uneq1d
    @47
    @21
    c0
    cun
    @21
    c0
    @21
    uncom
    @21
    un0
    eqtri
    syl6eq
    fveq2d
    @45
    @1
    @21
    cK
    cpsubsp
    cfv
    #
    wcel
    #
    @46
    @21
    wceq
    @42
    @1
    @15
    @44
    simplrl
    #
    @45
    cK
    cal
    wcel
    #
    @34
    @49
    @45
    @1
    @51
    @50
    cK
    hlatl
    syl
    @43
    @18
    @34
    simprr
    #
    cA
    @20
    @48
    cK
    pclfincl.a
    @48
    eqid
    #
    snatpsubN
    syl2anc
    @48
    cU
    cK
    chlt
    @21
    @53
    pclfincl.c
    pclidN
    syl2anc
    eqtrd
    @45
    @1
    @34
    @21
    cS
    wcel
    @50
    @52
    cA
    cS
    @20
    cK
    pclfincl.a
    pclfincl.s
    atpsubclN
    syl2anc
    eqeltrd
    exp43
    @33
    @14
    c0
    wne
    #
    wa
    #
    @16
    @18
    @34
    @26
    @55
    @16
    wa
    #
    @44
    wa
    #
    @25
    @17
    @21
    cK
    cpadd
    cfv
    #
    co
    #
    cS
    @57
    @25
    @59
    @57
    @25
    @59
    cU
    cfv
    #
    @59
    @57
    @1
    @22
    @59
    wss
    @59
    cA
    wss
    #
    @25
    @60
    wss
    @55
    @1
    @15
    @44
    simplrl
    #
    @57
    @22
    @17
    @21
    cun
    #
    @59
    @57
    @14
    @17
    wss
    #
    @22
    @63
    wss
    @16
    @64
    @55
    @44
    cA
    cU
    cK
    chlt
    @14
    pclfincl.a
    pclfincl.c
    pclssidN
    ad2antlr
    @14
    @17
    @21
    unss1
    syl
    @57
    @1
    @17
    cA
    wss
    #
    @37
    @63
    @59
    wss
    @62
    @57
    @1
    @18
    @65
    @62
    @56
    @18
    @34
    simprl
    #
    cA
    cS
    chlt
    cK
    @17
    pclfincl.a
    pclfincl.s
    psubclssatN
    syl2anc
    #
    @34
    @37
    @56
    @18
    @20
    cA
    snssi
    ad2antll
    #
    cA
    chlt
    @58
    cK
    @17
    @21
    pclfincl.a
    @58
    eqid
    #
    paddunssN
    syl3anc
    sstrd
    @57
    @1
    @65
    @37
    @61
    @62
    @67
    @68
    cA
    chlt
    @58
    cK
    @17
    @21
    pclfincl.a
    @69
    paddssat
    syl3anc
    cA
    cU
    cK
    chlt
    @22
    @59
    pclfincl.a
    pclfincl.c
    pclssN
    syl3anc
    @57
    @1
    @59
    @48
    wcel
    #
    @60
    @59
    wceq
    @62
    @57
    @1
    @59
    cS
    wcel
    #
    @70
    @62
    @57
    @1
    @18
    @34
    @71
    @62
    @66
    @56
    @18
    @34
    simprr
    #
    cA
    cS
    @58
    @20
    cK
    @17
    pclfincl.a
    @69
    pclfincl.s
    paddatclN
    syl3anc
    #
    cS
    @48
    cK
    @59
    @53
    pclfincl.s
    psubclsubN
    syl2anc
    @48
    cU
    cK
    chlt
    @59
    @53
    pclfincl.c
    pclidN
    syl2anc
    sseqtrd
    @57
    vq
    @59
    @25
    @57
    vq
    cv
    #
    @59
    wcel
    #
    @22
    vw
    cv
    #
    wss
    #
    vq
    vw
    wel
    #
    wi
    #
    vw
    @48
    wral
    #
    @74
    @25
    wcel
    #
    @57
    @75
    @79
    vw
    @48
    @57
    @75
    @74
    cA
    wcel
    #
    @74
    vp
    cv
    #
    @20
    cK
    cjn
    cfv
    #
    co
    cK
    cple
    cfv
    #
    wbr
    #
    vp
    @17
    wrex
    #
    wa
    #
    @76
    @48
    wcel
    #
    @79
    wi
    #
    @57
    cK
    clat
    wcel
    #
    @65
    @34
    @17
    c0
    wne
    #
    @75
    @88
    wb
    @57
    @1
    @91
    @62
    cK
    hllat
    syl
    @67
    @72
    @57
    @92
    @54
    @33
    @54
    @16
    @44
    simpllr
    @57
    @17
    c0
    @14
    c0
    @16
    @17
    c0
    wceq
    @41
    wb
    @55
    @44
    cA
    @14
    cU
    cK
    pclfincl.a
    pclfincl.c
    pcl0bN
    ad2antlr
    necon3bid
    mpbird
    cA
    @58
    @20
    @74
    @84
    cK
    @85
    @17
    vp
    @85
    eqid
    #
    @84
    eqid
    #
    pclfincl.a
    @69
    elpaddat
    syl31anc
    @57
    @82
    @87
    @90
    @56
    @44
    @82
    @87
    @90
    wi
    @56
    @44
    @82
    w3a
    #
    @86
    @90
    vp
    @17
    @95
    @83
    @17
    wcel
    #
    @86
    @89
    @77
    @78
    @95
    @96
    @86
    w3a
    #
    @89
    @77
    wa
    #
    wa
    #
    @1
    @89
    @82
    vp
    vw
    wel
    #
    vz
    vw
    wel
    #
    @86
    @78
    @97
    @1
    @98
    @95
    @96
    @1
    @86
    @1
    @15
    @55
    @44
    @82
    simp1rl
    3ad2ant1
    adantr
    #
    @97
    @89
    @77
    simprl
    #
    @56
    @44
    @82
    @96
    @86
    @98
    simpl13
    @99
    @1
    @14
    @76
    wss
    #
    @89
    @96
    @100
    @102
    @77
    @104
    @97
    @89
    @77
    @104
    @21
    @76
    wss
    #
    wa
    #
    @104
    @14
    @21
    @76
    unss
    #
    @104
    @105
    simpl
    sylbir
    ad2antll
    @103
    @95
    @96
    @86
    @98
    simpl2
    @83
    @48
    cU
    cK
    chlt
    @14
    @76
    @53
    pclfincl.c
    elpcliN
    syl31anc
    @77
    @101
    @97
    @89
    @77
    @106
    @101
    @107
    @105
    @101
    @104
    @101
    @105
    @20
    @76
    @38
    snss
    biimpri
    adantl
    sylbir
    ad2antll
    @95
    @96
    @86
    @98
    simpl3
    cA
    chlt
    @74
    @83
    @20
    @48
    @84
    cK
    @85
    @76
    @93
    @94
    pclfincl.a
    @53
    psubspi2N
    syl33anc
    exp520
    rexlimdv
    3expia
    impd
    sylbid
    ralrimdv
    @57
    @1
    @23
    @81
    @80
    wb
    @62
    @57
    @36
    @23
    @57
    @15
    @34
    @55
    @1
    @15
    @44
    simplrr
    @72
    jca
    @39
    sylib
    vw
    cA
    @74
    @48
    cU
    cK
    chlt
    @22
    pclfincl.a
    @53
    pclfincl.c
    vq
    vex
    elpclN
    syl2anc
    sylibrd
    ssrdv
    eqssd
    @73
    eqeltrd
    exp43
    pm2.61dane
    a2d
    imp4b
    syl5bi
    ex
    findcard2
    3impib
    3coml
end
