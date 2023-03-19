include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "co.mm"
include "wceq.mm"
include "cxr.mm"
include "cxp.mm"
include "cpw.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "ioof.mm"
include "ffn.mm"
include "ovelrn.mm"
include "mp2b.mm"
include "cpnf.mm"
include "cmnf.mm"
include "w3o.mm"
include "elxr.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "crab.mm"
include "simpr.mm"
include "elioore.mm"
include "anim12ci.mm"
include "icoreelrn.mm"
include "syl.mm"
include "adantl.mm"
include "leidd.mm"
include "w3a.mm"
include "rexrd.mm"
include "elioo1.mm"
include "syldan.mm"
include "biimpa.mm"
include "simp3d.mm"
include "cico.mm"
include "rexr.mm"
include "3anim1i.mm"
include "elico1.mm"
include "syl2an.mm"
include "biimprd.mm"
include "syl2im.mm"
include "icoreval.mm"
include "eleq2d.mm"
include "sylibd.mm"
include "mp3and.mm"
include "nfv.mm"
include "nfrab1.mm"
include "nfcv.mm"
include "iooval.mm"
include "anbi1d.mm"
include "pm5.32i.mm"
include "rabid.mm"
include "anbi12i.mm"
include "simpl.mm"
include "ad2antll.mm"
include "anim12i.mm"
include "anim2i.mm"
include "3anass.mm"
include "sylibr.mm"
include "simprl.mm"
include "xrltletr.mm"
include "sylc.mm"
include "simprr.mm"
include "jca.mm"
include "sylanbrc.mm"
include "adantlr.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "sylan2b.mm"
include "sylbi.mm"
include "expr.mm"
include "ssrd.mm"
include "sylanl2.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ancom1s.mm"
include "expl.mm"
include "c1.mm"
include "caddc.mm"
include "peano2re.mm"
include "syl2anc.mm"
include "ltp1d.mm"
include "jca32.mm"
include "breq2.mm"
include "breq1.mm"
include "elrab.mm"
include "simpll.mm"
include "elioopnf.mm"
include "simplbda.mm"
include "xrltletrd.mm"
include "mp2and.mm"
include "ex.mm"
include "syl5bi.mm"
include "oveq2.mm"
include "anbi2d.mm"
include "sseq2d.mm"
include "imbi12d.mm"
include "mpbiri.mm"
include "impl.mm"
include "nltmnf.mm"
include "intnand.mm"
include "eliooord.mm"
include "nsyl.mm"
include "pm2.21d.mm"
include "impd.mm"
include "ancomsd.mm"
include "mpcom.mm"
include "3jaoi.mm"
include "expdimp.mm"
include "ancoms.mm"
include "sseq2.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "rgen.mm"
include "rgenw.mm"
include "cuni.mm"
include "cvv.mm"
include "iooex.mm"
include "rnex.mm"
include "unirnioo.mm"
include "icoreunrn.mm"
include "eqtr3i.mm"
include "tgss2.mm"
include "mp2an.mm"
include "raleqi.mm"
include "bitr4i.mm"
include "mpbir.mm"

theorem relowlssretop
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vi: setvar i
  let vo: setvar o
  let vx: setvar x
  let vz: setvar z
  assume relowlssretop.1: |- I = ( [,) " ( RR X. RR ) )


  assert |- ( topGen ` ran (,) ) C_ ( topGen ` I )

  proof
    cioo
    crn
    #
    ctg
    cfv
    cI
    ctg
    cfv
    wss
    #
    vx
    cv
    #
    vo
    cv
    #
    wcel
    #
    @2
    vi
    cv
    #
    wcel
    #
    @5
    @3
    wss
    #
    wa
    #
    vi
    cI
    wrex
    #
    wi
    #
    vo
    @0
    wral
    #
    vx
    cr
    wral
    #
    @11
    vx
    cr
    @10
    vo
    @0
    @3
    @0
    wcel
    #
    @3
    va
    cv
    #
    vb
    cv
    #
    cioo
    co
    #
    wceq
    #
    vb
    cxr
    wrex
    va
    cxr
    wrex
    #
    @10
    cxr
    cxr
    cxp
    #
    cr
    cpw
    #
    cioo
    wf
    cioo
    @19
    wfn
    @13
    @18
    wb
    ioof
    @19
    @20
    cioo
    ffn
    va
    vb
    cxr
    cxr
    @3
    cioo
    ovelrn
    mp2b
    @17
    @10
    va
    vb
    cxr
    cxr
    @14
    cxr
    wcel
    #
    @15
    cxr
    wcel
    #
    wa
    #
    @10
    @17
    @2
    @16
    wcel
    #
    @6
    @5
    @16
    wss
    #
    wa
    #
    vi
    cI
    wrex
    #
    wi
    #
    @22
    @21
    @28
    @22
    @21
    @24
    @27
    @22
    @15
    cr
    wcel
    #
    @15
    cpnf
    wceq
    #
    @15
    cmnf
    wceq
    #
    w3o
    @21
    @24
    wa
    #
    @27
    wi
    #
    @15
    elxr
    @29
    @33
    @30
    @31
    @29
    @21
    @24
    @27
    @21
    @29
    @24
    @27
    @21
    @29
    wa
    #
    @24
    wa
    #
    @2
    vz
    cv
    #
    cle
    wbr
    #
    @36
    @15
    clt
    wbr
    #
    wa
    #
    vz
    cr
    crab
    #
    cI
    wcel
    #
    @2
    @40
    wcel
    #
    @40
    @16
    wss
    #
    @27
    @35
    @2
    cr
    wcel
    #
    @29
    wa
    #
    @41
    @34
    @29
    @24
    @44
    @21
    @29
    simpr
    #
    @2
    @14
    @15
    elioore
    #
    anim12ci
    #
    vz
    @2
    @15
    cI
    relowlssretop.1
    icoreelrn
    syl
    @35
    @44
    @2
    @2
    cle
    wbr
    #
    @2
    @15
    clt
    wbr
    #
    @42
    @24
    @44
    @34
    @47
    adantl
    @24
    @49
    @34
    @24
    @2
    @47
    leidd
    adantl
    @35
    @2
    cxr
    wcel
    #
    @14
    @2
    clt
    wbr
    #
    @50
    @34
    @24
    @51
    @52
    @50
    w3a
    #
    @21
    @29
    @22
    @24
    @53
    wb
    @34
    @15
    @46
    rexrd
    @14
    @15
    @2
    elioo1
    syldan
    biimpa
    simp3d
    @35
    @44
    @49
    @50
    w3a
    #
    @2
    @2
    @15
    cico
    co
    #
    wcel
    #
    @42
    @35
    @45
    @54
    @51
    @49
    @50
    w3a
    #
    @56
    @48
    @44
    @51
    @49
    @50
    @2
    rexr
    #
    3anim1i
    @45
    @56
    @57
    @44
    @51
    @22
    @56
    @57
    wb
    @29
    @58
    @15
    rexr
    #
    @2
    @15
    @2
    elico1
    syl2an
    biimprd
    syl2im
    @35
    @55
    @40
    @2
    @35
    @45
    @55
    @40
    wceq
    @48
    vz
    @2
    @15
    icoreval
    syl
    eleq2d
    sylibd
    mp3and
    @29
    @21
    @22
    @24
    @43
    @59
    @23
    @24
    wa
    #
    vz
    @40
    @16
    @60
    vz
    nfv
    @39
    vz
    cr
    nfrab1
    vz
    @16
    nfcv
    @23
    @24
    @36
    @40
    wcel
    #
    @36
    @16
    wcel
    #
    @23
    @24
    @61
    wa
    #
    wa
    @23
    @2
    @52
    @50
    wa
    #
    vx
    cxr
    crab
    #
    wcel
    #
    @61
    wa
    #
    wa
    @62
    @23
    @63
    @67
    @23
    @24
    @66
    @61
    @23
    @16
    @65
    @2
    vx
    @14
    @15
    iooval
    eleq2d
    anbi1d
    pm5.32i
    @67
    @23
    @51
    @64
    wa
    #
    @36
    cr
    wcel
    #
    @39
    wa
    #
    wa
    #
    @62
    @66
    @68
    @61
    @70
    @64
    vx
    cxr
    rabid
    @39
    vz
    cr
    rabid
    anbi12i
    @23
    @71
    wa
    @36
    @14
    @36
    clt
    wbr
    #
    @38
    wa
    #
    vz
    cxr
    crab
    #
    @16
    @21
    @71
    @36
    @74
    wcel
    #
    @22
    @21
    @71
    wa
    #
    @36
    cxr
    wcel
    #
    @73
    @75
    @70
    @77
    @21
    @68
    @70
    @36
    @69
    @39
    simpl
    rexrd
    #
    ad2antll
    @76
    @72
    @38
    @76
    @21
    @51
    @77
    w3a
    #
    @52
    @37
    wa
    #
    @72
    @76
    @21
    @51
    @77
    wa
    #
    wa
    @79
    @71
    @81
    @21
    @68
    @51
    @70
    @77
    @51
    @64
    simpl
    @78
    anim12i
    anim2i
    @21
    @51
    @77
    3anass
    sylibr
    @71
    @80
    @21
    @68
    @52
    @70
    @37
    @51
    @52
    @50
    simprl
    @69
    @37
    @38
    simprl
    anim12i
    adantl
    @14
    @2
    @36
    xrltletr
    sylc
    @70
    @38
    @21
    @68
    @69
    @37
    @38
    simprr
    ad2antll
    jca
    @73
    vz
    cxr
    rabid
    sylanbrc
    adantlr
    @23
    @16
    @74
    wceq
    @71
    vz
    @14
    @15
    iooval
    adantr
    eleqtrrd
    sylan2b
    sylbi
    expr
    ssrd
    sylanl2
    @26
    @42
    @43
    wa
    vi
    @40
    cI
    @5
    @40
    wceq
    @6
    @42
    @25
    @43
    @5
    @40
    @2
    eleq2
    @5
    @40
    @16
    sseq1
    anbi12d
    rspcev
    syl12anc
    ancom1s
    expl
    @30
    @21
    @24
    @27
    @21
    @30
    @24
    @27
    @21
    @30
    wa
    #
    @24
    wa
    #
    @37
    @36
    @2
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    vz
    cr
    crab
    #
    cI
    wcel
    #
    @2
    @87
    wcel
    #
    @87
    @16
    wss
    #
    wa
    #
    @27
    @83
    @44
    @84
    cr
    wcel
    #
    @88
    @24
    @44
    @82
    @47
    adantl
    #
    @83
    @44
    @92
    @93
    @2
    peano2re
    syl
    vz
    @2
    @84
    cI
    relowlssretop.1
    icoreelrn
    syl2anc
    @30
    @21
    @24
    @91
    @30
    @21
    @24
    @91
    @30
    @32
    @91
    wi
    @21
    @2
    @14
    cpnf
    cioo
    co
    #
    wcel
    #
    wa
    #
    @89
    @87
    @94
    wss
    #
    wa
    #
    wi
    @96
    @89
    @97
    @96
    @44
    @49
    @2
    @84
    clt
    wbr
    #
    wa
    #
    wa
    @89
    @96
    @44
    @49
    @99
    @95
    @44
    @21
    @2
    @14
    cpnf
    elioore
    adantl
    #
    @96
    @2
    @101
    leidd
    @96
    @2
    @101
    ltp1d
    jca32
    @86
    @100
    vz
    @2
    cr
    @36
    @2
    wceq
    @37
    @49
    @85
    @99
    @36
    @2
    @2
    cle
    breq2
    @36
    @2
    @84
    clt
    breq1
    anbi12d
    elrab
    sylibr
    @96
    vz
    @87
    @94
    @96
    vz
    nfv
    @86
    vz
    cr
    nfrab1
    vz
    @94
    nfcv
    @36
    @87
    wcel
    @69
    @86
    wa
    #
    @96
    @36
    @94
    wcel
    #
    @86
    vz
    cr
    rabid
    @96
    @102
    @103
    @96
    @102
    wa
    #
    @69
    @72
    @103
    @96
    @69
    @86
    simprl
    #
    @104
    @14
    @2
    @36
    @21
    @95
    @102
    simpll
    @104
    @2
    @96
    @44
    @102
    @101
    adantr
    rexrd
    @104
    @36
    @105
    rexrd
    @96
    @52
    @102
    @21
    @95
    @44
    @52
    @14
    @2
    elioopnf
    simplbda
    adantr
    @102
    @37
    @96
    @69
    @37
    @85
    simprl
    adantl
    xrltletrd
    @96
    @69
    @72
    wa
    #
    @103
    wi
    #
    @102
    @21
    @107
    @95
    @21
    @103
    @106
    @14
    @36
    elioopnf
    biimprd
    adantr
    adantr
    mp2and
    ex
    syl5bi
    ssrd
    jca
    @30
    @32
    @96
    @91
    @98
    @30
    @24
    @95
    @21
    @30
    @16
    @94
    @2
    @15
    cpnf
    @14
    cioo
    oveq2
    #
    eleq2d
    anbi2d
    @30
    @90
    @97
    @89
    @30
    @16
    @94
    @87
    @108
    sseq2d
    anbi2d
    imbi12d
    mpbiri
    impl
    ancom1s
    @26
    @91
    vi
    @87
    cI
    @5
    @87
    wceq
    @6
    @89
    @25
    @90
    @5
    @87
    @2
    eleq2
    @5
    @87
    @16
    sseq1
    anbi12d
    rspcev
    syl2anc
    ancom1s
    expl
    @31
    @21
    @24
    @27
    @21
    @31
    @24
    @27
    @44
    @21
    @31
    wa
    #
    @24
    wa
    #
    @27
    @24
    @44
    @109
    @47
    adantl
    @44
    @51
    @110
    @27
    wi
    @58
    @110
    @109
    @2
    @14
    cmnf
    cioo
    co
    #
    wcel
    #
    wa
    @51
    @27
    @109
    @24
    @112
    @31
    @24
    @112
    wb
    @21
    @31
    @16
    @111
    @2
    @15
    cmnf
    @14
    cioo
    oveq2
    eleq2d
    adantl
    pm5.32i
    @51
    @112
    @109
    @27
    @51
    @112
    @109
    @27
    @51
    @112
    @109
    @27
    wi
    @51
    @52
    @2
    cmnf
    clt
    wbr
    #
    wa
    @112
    @51
    @113
    @52
    @2
    nltmnf
    intnand
    @2
    @14
    cmnf
    eliooord
    nsyl
    pm2.21d
    impd
    ancomsd
    syl5bi
    syl
    mpcom
    ancom1s
    expl
    3jaoi
    sylbi
    expdimp
    ancoms
    @17
    @4
    @24
    @9
    @27
    @3
    @16
    @2
    eleq2
    @17
    @8
    @26
    vi
    cI
    @17
    @7
    @25
    @6
    @3
    @16
    @5
    sseq2
    anbi2d
    rexbidv
    imbi12d
    syl5ibrcom
    rexlimivv
    sylbi
    rgen
    rgenw
    @1
    @11
    vx
    @0
    cuni
    #
    wral
    #
    @12
    @0
    cvv
    wcel
    @114
    cI
    cuni
    #
    wceq
    @1
    @115
    wb
    cioo
    iooex
    rnex
    cr
    @114
    @116
    unirnioo
    cI
    relowlssretop.1
    icoreunrn
    eqtr3i
    vx
    vo
    vi
    @0
    cI
    cvv
    tgss2
    mp2an
    @11
    vx
    cr
    @114
    unirnioo
    raleqi
    bitr4i
    mpbir
end
