include "crn.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "csumge0.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "ccom.mm"
include "cvv.mm"
include "nfv.mm"
include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "jca.mm"
include "fex.mm"
include "rnexg.mm"
include "3syl.mm"
include "difssd.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "meaf.mm"
include "adantr.mm"
include "wss.mm"
include "frn.mm"
include "syl.mm"
include "sselda.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "wceq.mm"
include "simpl.mm"
include "cin.mm"
include "id.mm"
include "dfin4.mm"
include "eqcomi.mm"
include "syl6eleq.mm"
include "elinel2.mm"
include "elsni.mm"
include "adantl.mm"
include "simpr.mm"
include "fveq2d.mm"
include "mea0.mm"
include "eqtrd.mm"
include "syl2anc.mm"
include "sge0ss.mm"
include "eqcomd.mm"
include "feqresmpt.mm"
include "ffvelrnda.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "wne.mm"
include "crab.mm"
include "ssrab2.mm"
include "a1i.mm"
include "syl5eqss.mm"
include "wn.mm"
include "eldifi.mm"
include "ad2antlr.mm"
include "cmea.mm"
include "ad4ant14.mm"
include "neneq.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "neeq1d.mm"
include "elrab.mm"
include "sylibr.mm"
include "syl6eleqr.mm"
include "eldifn.mm"
include "nne.mm"
include "sylib.mm"
include "ssexd.mm"
include "wf1.mm"
include "wf1o.mm"
include "eqid.mm"
include "wfn.mm"
include "ffnd.mm"
include "dffn3.mm"
include "eleq2i.mm"
include "rabid.mm"
include "bitri.mm"
include "biimpi.mm"
include "simprd.mm"
include "nelsn.mm"
include "eldifd.mm"
include "wdisj.mm"
include "disjss1.mm"
include "sylc.mm"
include "disjf1.mm"
include "wb.mm"
include "f1eq1.mm"
include "mpbird.mm"
include "rneqd.mm"
include "wral.mm"
include "ralrimiva.mm"
include "rnmptss.mm"
include "eqsstrd.mm"
include "eldifsni.mm"
include "w3a.mm"
include "wrex.mm"
include "fvelrnb.mm"
include "mpbid.mm"
include "3adant3.mm"
include "wi.mm"
include "3ad2ant3.mm"
include "simp1l.mm"
include "simp2.mm"
include "eqnetrd.mm"
include "adantll.mm"
include "3adant2.mm"
include "biimpri.mm"
include "fvexd.mm"
include "elrnmpt1.mm"
include "3adant1.mm"
include "3ad2ant1.mm"
include "eleqtrd.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "dfss3.mm"
include "eqssd.mm"
include "dff1o5.mm"
include "fvres.mm"
include "sge0f1o.mm"
include "3eqtrd.mm"
include "3eqtr4d.mm"

theorem meadjiunlem
  let wph: wff ph
  let cS: class S
  let vi: setvar i
  let cG: class G
  let cM: class M
  let cV: class V
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume meadjiunlem.f: |- ( ph -> M e. Meas )
  assume meadjiunlem.3: |- S = dom M
  assume meadjiunlem.x: |- ( ph -> X e. V )
  assume meadjiunlem.g: |- ( ph -> G : X --> S )
  assume meadjiunlem.y: |- Y = { i e. X | ( G ` i ) =/= (/) }
  assume meadjiunlem.dj: |- ( ph -> Disj_ i e. X ( G ` i ) )

  disjoint G i
  disjoint X i
  disjoint Y i
  disjoint i ph
  disjoint G j
  disjoint i j
  disjoint G k
  disjoint j k
  disjoint G x
  disjoint i x
  disjoint M j
  disjoint M k
  disjoint S j
  disjoint S k
  disjoint X j
  disjoint Y j
  disjoint Y k
  disjoint Y x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( M |` ran G ) ) = ( sum^ ` ( M o. G ) ) )

  proof
    wph
    vk
    cG
    crn
    #
    vk
    cv
    #
    cM
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    vk
    @0
    c0
    csn
    #
    cdif
    #
    @2
    cmpt
    csumge0
    cfv
    #
    cM
    @0
    cres
    #
    csumge0
    cfv
    cM
    cG
    ccom
    #
    csumge0
    cfv
    #
    wph
    @7
    @4
    wph
    @6
    @0
    @2
    vk
    cvv
    wph
    vk
    nfv
    #
    wph
    cX
    cS
    cG
    wf
    #
    cX
    cV
    wcel
    #
    wa
    cG
    cvv
    wcel
    @0
    cvv
    wcel
    wph
    @12
    @13
    meadjiunlem.g
    meadjiunlem.x
    jca
    cX
    cS
    cV
    cG
    fex
    cG
    cvv
    rnexg
    3syl
    wph
    @0
    @5
    difssd
    #
    wph
    @1
    @6
    wcel
    #
    wa
    #
    cS
    cc0
    cpnf
    cicc
    co
    #
    @1
    cM
    wph
    cS
    @17
    cM
    wf
    #
    @15
    wph
    cS
    cM
    meadjiunlem.f
    meadjiunlem.3
    meaf
    #
    adantr
    @16
    @0
    cS
    @1
    wph
    @0
    cS
    wss
    #
    @15
    wph
    @12
    @20
    meadjiunlem.g
    cX
    cS
    cG
    frn
    syl
    #
    adantr
    wph
    @6
    @0
    @1
    @14
    sselda
    sseldd
    ffvelrnd
    #
    wph
    @1
    @0
    @6
    cdif
    #
    wcel
    #
    wa
    wph
    @1
    c0
    wceq
    #
    @2
    cc0
    wceq
    wph
    @24
    simpl
    @24
    @25
    wph
    @24
    @1
    @0
    @5
    cin
    #
    wcel
    #
    @25
    @24
    @1
    @23
    @26
    @24
    id
    @26
    @23
    @0
    @5
    dfin4
    eqcomi
    syl6eleq
    @27
    @1
    @5
    wcel
    @25
    @1
    @0
    @5
    elinel2
    @1
    c0
    elsni
    syl
    syl
    adantl
    wph
    @25
    wa
    #
    @2
    c0
    cM
    cfv
    #
    cc0
    @28
    @1
    c0
    cM
    wph
    @25
    simpr
    fveq2d
    wph
    @29
    cc0
    wceq
    @25
    wph
    cM
    meadjiunlem.f
    mea0
    adantr
    eqtrd
    syl2anc
    sge0ss
    eqcomd
    wph
    @8
    @3
    csumge0
    wph
    vk
    cS
    @17
    @0
    cM
    @19
    @21
    feqresmpt
    fveq2d
    wph
    @10
    vj
    cX
    vj
    cv
    #
    cG
    cfv
    #
    cM
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    vj
    cY
    @32
    cmpt
    csumge0
    cfv
    #
    @7
    wph
    @9
    @33
    csumge0
    wph
    vj
    vk
    cX
    cS
    @31
    @2
    @32
    cG
    cM
    wph
    cX
    cS
    @30
    cG
    meadjiunlem.g
    ffvelrnda
    wph
    vj
    cX
    cS
    cG
    meadjiunlem.g
    feqmptd
    wph
    vk
    cS
    @17
    cM
    @19
    feqmptd
    @1
    @31
    cM
    fveq2
    #
    fmptco
    fveq2d
    wph
    @35
    @34
    wph
    cY
    cX
    @32
    vj
    cV
    wph
    vj
    nfv
    #
    meadjiunlem.x
    wph
    cY
    vi
    cv
    #
    cG
    cfv
    #
    c0
    wne
    #
    vi
    cX
    crab
    #
    cX
    meadjiunlem.y
    @41
    cX
    wss
    wph
    @40
    vi
    cX
    ssrab2
    a1i
    syl5eqss
    #
    wph
    @30
    cY
    wcel
    #
    wa
    #
    cS
    @17
    @31
    cM
    wph
    @18
    @43
    @19
    adantr
    @44
    cX
    cS
    @30
    cG
    wph
    @12
    @43
    meadjiunlem.g
    adantr
    wph
    cY
    cX
    @30
    @42
    sselda
    ffvelrnd
    ffvelrnd
    wph
    @30
    cX
    cY
    cdif
    wcel
    #
    wa
    #
    @32
    cc0
    wne
    #
    wn
    @32
    cc0
    wceq
    #
    @46
    @47
    @43
    @46
    @47
    wa
    #
    @30
    @41
    cY
    @49
    @30
    cX
    wcel
    #
    @31
    c0
    wne
    #
    wa
    @30
    @41
    wcel
    @49
    @50
    @51
    @45
    @50
    wph
    @47
    @30
    cX
    cY
    eldifi
    ad2antlr
    @49
    @31
    c0
    @49
    @31
    c0
    wceq
    #
    @48
    wph
    @52
    @48
    @45
    @47
    wph
    @52
    wa
    #
    @32
    @29
    cc0
    @52
    @32
    @29
    wceq
    wph
    @31
    c0
    cM
    fveq2
    adantl
    @53
    cM
    wph
    cM
    cmea
    wcel
    @52
    meadjiunlem.f
    adantr
    mea0
    eqtrd
    ad4ant14
    @47
    @48
    wn
    @46
    @52
    @32
    cc0
    neneq
    ad2antlr
    pm2.65da
    neqned
    jca
    @40
    @51
    vi
    @30
    cX
    @38
    @30
    wceq
    @39
    @31
    c0
    @38
    @30
    cG
    fveq2
    neeq1d
    elrab
    sylibr
    meadjiunlem.y
    syl6eleqr
    @45
    @43
    wn
    wph
    @47
    @30
    cX
    cY
    eldifn
    ad2antlr
    pm2.65da
    @32
    cc0
    nne
    sylib
    sge0ss
    eqcomd
    wph
    @7
    @35
    wph
    @6
    @2
    cY
    @32
    vk
    vj
    cG
    cY
    cres
    #
    @31
    cvv
    @11
    @37
    @36
    wph
    cY
    cX
    cV
    meadjiunlem.x
    @42
    ssexd
    wph
    cY
    @6
    @54
    wf1
    #
    @54
    crn
    #
    @6
    wceq
    #
    wa
    cY
    @6
    @54
    wf1o
    wph
    @55
    @57
    wph
    @55
    cY
    @6
    vi
    cY
    @39
    cmpt
    #
    wf1
    #
    wph
    vi
    cY
    @39
    @58
    @6
    wph
    vi
    nfv
    @58
    eqid
    #
    wph
    @38
    cY
    wcel
    #
    wa
    #
    @39
    @0
    @5
    @62
    cX
    @0
    @38
    cG
    wph
    cX
    @0
    cG
    wf
    #
    @61
    wph
    cG
    cX
    wfn
    #
    @63
    wph
    cX
    cS
    cG
    meadjiunlem.g
    ffnd
    #
    cX
    cG
    dffn3
    sylib
    adantr
    wph
    cY
    cX
    @38
    @42
    sselda
    ffvelrnd
    @62
    @40
    @39
    @5
    wcel
    wn
    @61
    @40
    wph
    @61
    @38
    cX
    wcel
    #
    @40
    @61
    @66
    @40
    wa
    #
    @61
    @38
    @41
    wcel
    @67
    cY
    @41
    @38
    meadjiunlem.y
    eleq2i
    @40
    vi
    cX
    rabid
    bitri
    #
    biimpi
    simprd
    adantl
    #
    @39
    c0
    nelsn
    syl
    eldifd
    #
    @69
    wph
    cY
    cX
    wss
    vi
    cX
    @39
    wdisj
    vi
    cY
    @39
    wdisj
    @42
    meadjiunlem.dj
    vi
    cY
    cX
    @39
    disjss1
    sylc
    disjf1
    wph
    @54
    @58
    wceq
    @55
    @59
    wb
    wph
    vi
    cX
    cS
    cY
    cG
    meadjiunlem.g
    @42
    feqresmpt
    #
    cY
    @6
    @54
    @58
    f1eq1
    syl
    mpbird
    wph
    @56
    @6
    wph
    @56
    @58
    crn
    #
    @6
    wph
    @54
    @58
    @71
    rneqd
    #
    wph
    @39
    @6
    wcel
    #
    vi
    cY
    wral
    @72
    @6
    wss
    wph
    @74
    vi
    cY
    @70
    ralrimiva
    vi
    cY
    @39
    @6
    @58
    @60
    rnmptss
    syl
    eqsstrd
    wph
    vx
    cv
    #
    @56
    wcel
    #
    vx
    @6
    wral
    @6
    @56
    wss
    wph
    @76
    vx
    @6
    wph
    @75
    @6
    wcel
    #
    wa
    wph
    @75
    @0
    wcel
    #
    @75
    c0
    wne
    #
    @76
    wph
    @77
    simpl
    @77
    @78
    wph
    @75
    @0
    @5
    eldifi
    adantl
    @77
    @79
    wph
    @75
    @0
    c0
    eldifsni
    adantl
    wph
    @78
    @79
    w3a
    @39
    @75
    wceq
    #
    vi
    cX
    wrex
    #
    @76
    wph
    @78
    @81
    @79
    wph
    @78
    wa
    @78
    @81
    wph
    @78
    simpr
    wph
    @78
    @81
    wb
    #
    @78
    wph
    @64
    @82
    @65
    vi
    cX
    @75
    cG
    fvelrnb
    syl
    adantr
    mpbid
    3adant3
    wph
    @79
    @81
    @76
    wi
    @78
    wph
    @79
    wa
    #
    @80
    @76
    vi
    cX
    @83
    @66
    @80
    @76
    @83
    @66
    @80
    w3a
    #
    @75
    @39
    @56
    @80
    @83
    @75
    @39
    wceq
    @66
    @80
    @39
    @75
    @80
    id
    eqcomd
    3ad2ant3
    @84
    wph
    @66
    @40
    @39
    @56
    wcel
    wph
    @79
    @66
    @80
    simp1l
    @83
    @66
    @80
    simp2
    @83
    @80
    @40
    @66
    @79
    @80
    @40
    wph
    @79
    @80
    wa
    @39
    @75
    c0
    @79
    @80
    simpr
    @79
    @80
    simpl
    eqnetrd
    adantll
    3adant2
    wph
    @66
    @40
    w3a
    @39
    @72
    @56
    @66
    @40
    @39
    @72
    wcel
    #
    wph
    @67
    @61
    @39
    cvv
    wcel
    @85
    @61
    @67
    @68
    biimpri
    @67
    @38
    cG
    fvexd
    vi
    cY
    @39
    @58
    cvv
    @60
    elrnmpt1
    syl2anc
    3adant1
    wph
    @66
    @72
    @56
    wceq
    @40
    wph
    @56
    @72
    @73
    eqcomd
    3ad2ant1
    eleqtrd
    syl3anc
    eqeltrd
    3exp
    rexlimdv
    3adant2
    mpd
    syl3anc
    ralrimiva
    vx
    @6
    @56
    dfss3
    sylibr
    eqssd
    jca
    cY
    @6
    @54
    dff1o5
    sylibr
    @43
    @30
    @54
    cfv
    @31
    wceq
    wph
    @30
    cY
    cG
    fvres
    adantl
    @22
    sge0f1o
    eqcomd
    3eqtrd
    3eqtr4d
end
