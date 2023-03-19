include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "clspn.mm"
include "wceq.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "csca.mm"
include "c0g.mm"
include "wral.mm"
include "wf.mm"
include "eqid.mm"
include "uvcff.mm"
include "frn.mm"
include "syl.mm"
include "csupp.mm"
include "crab.mm"
include "cima.mm"
include "frlmbasf.mm"
include "adantll.mm"
include "cdm.mm"
include "suppssdm.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "ralrimiva.mm"
include "rabid2.mm"
include "sylibr.mm"
include "ssid.mm"
include "frlmsslsp.mm"
include "mp3an3.mm"
include "wfn.mm"
include "ffn.mm"
include "fnima.mm"
include "3syl.mm"
include "fveq2d.mm"
include "3eqtr2rd.mm"
include "simpll.mm"
include "simplr.mm"
include "difssd.mm"
include "vsnid.mm"
include "snssi.mm"
include "ad2antrl.mm"
include "dfss4.mm"
include "sylib.mm"
include "syl5eleqr.mm"
include "frlmsca.mm"
include "sneqd.mm"
include "difeq12d.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "adantrl.mm"
include "frlmssuvc2.mm"
include "wf1.mm"
include "ccnv.mm"
include "wfun.mm"
include "cnzr.mm"
include "ringelnzr.mm"
include "syl2anc.mm"
include "uvcf1.mm"
include "df-f1.mm"
include "simprbi.mm"
include "imadif.mm"
include "f1fn.mm"
include "simprl.mm"
include "fnsnfv.mm"
include "eqcomd.mm"
include "eqtr2d.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "neleqtrrd.mm"
include "ralrimivva.mm"
include "wb.mm"
include "oveq2.mm"
include "sneq.mm"
include "difeq2d.mm"
include "eleq12d.mm"
include "notbid.mm"
include "ralbidv.mm"
include "ralrn.mm"
include "mpbird.mm"
include "cvv.mm"
include "w3a.mm"
include "cfrlm.mm"
include "ovex.mm"
include "eqeltri.mm"
include "islbs.mm"
include "ax-mp.mm"
include "syl3anbrc.mm"

theorem frlmlbs
  let cR: class R
  let cU: class U
  let cF: class F
  let cI: class I
  let cJ: class J
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume frlmlbs.f: |- F = ( R freeLMod I )
  assume frlmlbs.u: |- U = ( R unitVec I )
  assume frlmlbs.j: |- J = ( LBasis ` F )


  assert |- ( ( R e. Ring /\ I e. V ) -> ran U e. J )

  proof
    cR
    crg
    wcel
    #
    cI
    cV
    wcel
    #
    wa
    #
    cU
    crn
    #
    cF
    cbs
    cfv
    #
    wss
    #
    @3
    cF
    clspn
    cfv
    #
    cfv
    #
    @4
    wceq
    #
    vb
    cv
    #
    va
    cv
    #
    cF
    cvsca
    cfv
    #
    co
    #
    @3
    @10
    csn
    #
    cdif
    #
    @6
    cfv
    #
    wcel
    #
    wn
    #
    vb
    cF
    csca
    cfv
    #
    cbs
    cfv
    #
    @18
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wral
    #
    va
    @3
    wral
    #
    @3
    cJ
    wcel
    #
    @2
    cI
    @4
    cU
    wf
    #
    @5
    @4
    cR
    cU
    cI
    cV
    cF
    frlmlbs.u
    frlmlbs.f
    @4
    eqid
    #
    uvcff
    #
    cI
    @4
    cU
    frn
    syl
    @2
    @4
    @10
    cR
    c0g
    cfv
    #
    csupp
    co
    #
    cI
    wss
    #
    va
    @4
    crab
    #
    cU
    cI
    cima
    #
    @6
    cfv
    #
    @7
    @2
    @31
    va
    @4
    wral
    @4
    @32
    wceq
    @2
    @31
    va
    @4
    @2
    @10
    @4
    wcel
    #
    wa
    cI
    cR
    cbs
    cfv
    #
    @10
    wf
    #
    @31
    @1
    @35
    @37
    @0
    @4
    cR
    cF
    cI
    @36
    cV
    @10
    frlmlbs.f
    @36
    eqid
    #
    @27
    frlmbasf
    adantll
    @37
    @10
    cdm
    @30
    cI
    @10
    @29
    suppssdm
    cI
    @36
    @10
    fdm
    syl5sseq
    syl
    ralrimiva
    @31
    va
    @4
    rabid2
    sylibr
    @0
    @1
    cI
    cI
    wss
    @34
    @32
    wceq
    cI
    ssid
    va
    @4
    @32
    cR
    cU
    cI
    cI
    @6
    cV
    cF
    @29
    frlmlbs.f
    frlmlbs.u
    @6
    eqid
    #
    @27
    @29
    eqid
    #
    @32
    eqid
    frlmsslsp
    mp3an3
    @2
    @33
    @3
    @6
    @2
    @26
    cU
    cI
    wfn
    #
    @33
    @3
    wceq
    #
    @28
    cI
    @4
    cU
    ffn
    #
    cI
    cU
    fnima
    #
    3syl
    fveq2d
    3eqtr2rd
    @2
    @24
    @9
    vc
    cv
    #
    cU
    cfv
    #
    @11
    co
    #
    @3
    @46
    csn
    #
    cdif
    #
    @6
    cfv
    #
    wcel
    #
    wn
    #
    vb
    @22
    wral
    #
    vc
    cI
    wral
    #
    @2
    @52
    vc
    vb
    cI
    @22
    @2
    @45
    cI
    wcel
    #
    @9
    @22
    wcel
    #
    wa
    #
    wa
    #
    @50
    @30
    cI
    @45
    csn
    #
    cdif
    #
    wss
    va
    @4
    crab
    #
    @47
    @58
    va
    @4
    @61
    cR
    @11
    cU
    cF
    cI
    @60
    @36
    @45
    cV
    @9
    @29
    frlmlbs.f
    frlmlbs.u
    @27
    @38
    @11
    eqid
    #
    @40
    @61
    eqid
    #
    @0
    @1
    @57
    simpll
    #
    @0
    @1
    @57
    simplr
    #
    @58
    cI
    @59
    difssd
    #
    @58
    @45
    @59
    cI
    @60
    cdif
    #
    vc
    vsnid
    @58
    @59
    cI
    wss
    #
    @67
    @59
    wceq
    @55
    @68
    @2
    @56
    @45
    cI
    snssi
    ad2antrl
    @59
    cI
    dfss4
    sylib
    syl5eleqr
    @2
    @56
    @9
    @36
    @29
    csn
    #
    cdif
    #
    wcel
    #
    @55
    @2
    @71
    @56
    @2
    @70
    @22
    @9
    @2
    @36
    @19
    @69
    @21
    @2
    cR
    @18
    cbs
    cR
    cF
    cI
    crg
    cV
    frlmlbs.f
    frlmsca
    #
    fveq2d
    @2
    @29
    @20
    @2
    cR
    @18
    c0g
    @72
    fveq2d
    sneqd
    difeq12d
    eleq2d
    biimpar
    adantrl
    #
    frlmssuvc2
    @58
    @50
    cU
    @60
    cima
    #
    @6
    cfv
    #
    @61
    @58
    @49
    @74
    @6
    @58
    @74
    @33
    cU
    @59
    cima
    #
    cdif
    #
    @49
    @58
    cI
    @4
    cU
    wf1
    #
    cU
    ccnv
    wfun
    #
    @74
    @77
    wceq
    @58
    cR
    cnzr
    wcel
    #
    @1
    @78
    @58
    @0
    @71
    @80
    @64
    @73
    @36
    cR
    @9
    @29
    @40
    @38
    ringelnzr
    syl2anc
    @65
    @4
    cR
    cU
    cI
    cV
    cF
    frlmlbs.u
    frlmlbs.f
    @27
    uvcf1
    syl2anc
    #
    @78
    @26
    @79
    cI
    @4
    cU
    df-f1
    simprbi
    cI
    @59
    cU
    imadif
    3syl
    @58
    @33
    @3
    @76
    @48
    @58
    @78
    @41
    @42
    @81
    cI
    @4
    cU
    f1fn
    #
    @44
    3syl
    @58
    @48
    @76
    @58
    @41
    @55
    @48
    @76
    wceq
    @58
    @78
    @41
    @81
    @82
    syl
    @2
    @55
    @56
    simprl
    cI
    @45
    cU
    fnsnfv
    syl2anc
    eqcomd
    difeq12d
    eqtr2d
    fveq2d
    @58
    @0
    @1
    @60
    cI
    wss
    @75
    @61
    wceq
    @64
    @65
    @66
    va
    @4
    @61
    cR
    cU
    cI
    @60
    @6
    cV
    cF
    @29
    frlmlbs.f
    frlmlbs.u
    @39
    @27
    @40
    @63
    frlmsslsp
    syl3anc
    eqtrd
    neleqtrrd
    ralrimivva
    @2
    @26
    @41
    @24
    @54
    wb
    @28
    @43
    @23
    @53
    va
    vc
    cI
    cU
    @10
    @46
    wceq
    #
    @17
    @52
    vb
    @22
    @83
    @16
    @51
    @83
    @12
    @47
    @15
    @50
    @10
    @46
    @9
    @11
    oveq2
    @83
    @14
    @49
    @6
    @83
    @13
    @48
    @3
    @10
    @46
    sneq
    difeq2d
    fveq2d
    eleq12d
    notbid
    ralbidv
    ralrn
    3syl
    mpbird
    cF
    cvv
    wcel
    @25
    @5
    @8
    @24
    w3a
    wb
    cF
    cR
    cI
    cfrlm
    co
    cvv
    frlmlbs.f
    cR
    cI
    cfrlm
    ovex
    eqeltri
    va
    vb
    @3
    @11
    @18
    cJ
    @19
    @6
    @4
    cF
    cvv
    @20
    @27
    @18
    eqid
    @62
    @19
    eqid
    frlmlbs.j
    @39
    @20
    eqid
    islbs
    ax-mp
    syl3anbrc
end
