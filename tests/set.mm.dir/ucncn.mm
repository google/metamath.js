include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "wbr.mm"
include "wi.mm"
include "cuss.mm"
include "wrex.mm"
include "cucn.mm"
include "wa.mm"
include "cust.mm"
include "wb.mm"
include "cusp.mm"
include "cutop.mm"
include "wceq.mm"
include "eqid.mm"
include "isusp.mm"
include "simplbi.mm"
include "syl.mm"
include "isucn.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simpld.mm"
include "wss.mm"
include "csn.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "adantr.mm"
include "syl5sseq.mm"
include "simplll.mm"
include "simpr.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "sseldd.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "r19.12.mm"
include "syl21anc.mm"
include "wrel.mm"
include "ad3antrrr.mm"
include "ad5antr.mm"
include "ustrel.mm"
include "ustimasn.mm"
include "syl3anc.mm"
include "simpllr.mm"
include "elrelimasn.mm"
include "biimpar.mm"
include "adantlr.mm"
include "wfn.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "ad7antr.mm"
include "mpbir2and.mm"
include "ex.mm"
include "ralrimiva.mm"
include "r19.26.mm"
include "pm3.33.mm"
include "ralimi.mm"
include "sylbir.mm"
include "w3a.mm"
include "simpl2l.mm"
include "biimpa.mm"
include "simpl2r.mm"
include "simpl3.mm"
include "breq2.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "mpd.mm"
include "ssrdv.mm"
include "syl121anc.mm"
include "reximdva.mm"
include "simprbi.mm"
include "eleqtrd.mm"
include "elutop.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "r19.29a.mm"
include "eleq2d.mm"
include "bitrd.mm"
include "ctopon.mm"
include "ctps.mm"
include "istps.mm"
include "sylib.mm"
include "iscn.mm"

theorem ucncn
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cF: class F
  let cJ: class J
  let cK: class K
  let va: setvar a
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ucncn.j: |- J = ( TopOpen ` R )
  assume ucncn.k: |- K = ( TopOpen ` S )
  assume ucncn.1: |- ( ph -> R e. UnifSp )
  assume ucncn.2: |- ( ph -> S e. UnifSp )
  assume ucncn.3: |- ( ph -> R e. TopSp )
  assume ucncn.4: |- ( ph -> S e. TopSp )
  assume ucncn.5: |- ( ph -> F e. ( ( UnifSt ` R ) uCn ( UnifSt ` S ) ) )


  assert |- ( ph -> F e. ( J Cn K ) )

  proof
    wph
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cR
    cbs
    cfv
    #
    cS
    cbs
    cfv
    #
    cF
    wf
    #
    cF
    ccnv
    va
    cv
    #
    cima
    #
    cJ
    wcel
    #
    va
    cK
    wral
    #
    wph
    @3
    vx
    cv
    #
    vz
    cv
    #
    vr
    cv
    #
    wbr
    #
    @8
    cF
    cfv
    #
    @9
    cF
    cfv
    #
    vs
    cv
    #
    wbr
    #
    wi
    #
    vz
    @1
    wral
    #
    vx
    @1
    wral
    vr
    cR
    cuss
    cfv
    #
    wrex
    #
    vs
    cS
    cuss
    cfv
    #
    wral
    #
    wph
    cF
    @18
    @20
    cucn
    co
    wcel
    #
    @3
    @21
    wa
    #
    ucncn.5
    wph
    @18
    @1
    cust
    cfv
    wcel
    #
    @20
    @2
    cust
    cfv
    wcel
    #
    @22
    @23
    wb
    wph
    cR
    cusp
    wcel
    #
    @24
    ucncn.1
    @26
    @24
    cJ
    @18
    cutop
    cfv
    #
    wceq
    #
    @1
    @18
    cJ
    cR
    @1
    eqid
    #
    @18
    eqid
    ucncn.j
    isusp
    #
    simplbi
    syl
    #
    wph
    cS
    cusp
    wcel
    #
    @25
    ucncn.2
    @32
    @25
    cK
    @20
    cutop
    cfv
    #
    wceq
    #
    @2
    @20
    cK
    cS
    @2
    eqid
    #
    @20
    eqid
    ucncn.k
    isusp
    #
    simplbi
    syl
    #
    vx
    vz
    @18
    cF
    @20
    @1
    @2
    vs
    vr
    isucn
    syl2anc
    mpbid
    #
    simpld
    #
    wph
    @6
    va
    cK
    wph
    @4
    cK
    wcel
    #
    wa
    #
    @6
    @5
    @1
    wss
    #
    @10
    @8
    csn
    cima
    #
    @5
    wss
    #
    vr
    @18
    wrex
    #
    vx
    @5
    wral
    #
    @41
    cF
    cdm
    #
    @5
    @1
    cF
    @4
    cnvimass
    wph
    @47
    @1
    wceq
    #
    @40
    wph
    @3
    @48
    @39
    @1
    @2
    cF
    fdm
    syl
    adantr
    syl5sseq
    #
    @41
    @45
    vx
    @5
    @41
    @8
    @5
    wcel
    #
    wa
    #
    @14
    @12
    csn
    #
    cima
    #
    @4
    wss
    #
    @45
    vs
    @20
    @51
    @14
    @20
    wcel
    #
    wa
    #
    @54
    wa
    #
    @17
    vr
    @18
    wrex
    #
    @45
    @56
    @58
    @54
    @56
    wph
    @55
    @8
    @1
    wcel
    #
    @58
    wph
    @40
    @50
    @55
    simplll
    #
    @51
    @55
    simpr
    @56
    @5
    @1
    @8
    @41
    @42
    @50
    @55
    @49
    ad2antrr
    @41
    @50
    @55
    simplr
    sseldd
    #
    wph
    @55
    wa
    #
    @58
    vx
    @1
    @62
    @19
    @58
    vx
    @1
    wral
    wph
    @19
    vs
    @20
    wph
    @3
    @21
    @38
    simprd
    r19.21bi
    @17
    vr
    vx
    @18
    @1
    r19.12
    syl
    r19.21bi
    syl21anc
    adantr
    @57
    @17
    @44
    vr
    @18
    @57
    @10
    @18
    wcel
    #
    wa
    #
    @17
    @44
    @64
    @17
    wa
    #
    wph
    @10
    wrel
    #
    @43
    @1
    wss
    #
    @11
    @9
    @5
    wcel
    #
    wi
    #
    vz
    @1
    wral
    #
    @44
    @56
    wph
    @54
    @63
    @17
    @60
    ad3antrrr
    #
    @64
    @66
    @17
    @64
    @24
    @63
    @66
    wph
    @24
    @40
    @50
    @55
    @54
    @63
    @31
    ad5antr
    @57
    @63
    simpr
    @18
    @10
    @1
    ustrel
    syl2anc
    adantr
    @65
    @24
    @63
    @59
    @67
    @65
    wph
    @24
    @71
    @31
    syl
    @57
    @63
    @17
    simplr
    @56
    @59
    @54
    @63
    @17
    @61
    ad3antrrr
    @8
    @18
    @10
    @1
    ustimasn
    syl3anc
    @65
    @17
    @15
    @68
    wi
    #
    vz
    @1
    wral
    #
    @70
    @64
    @17
    simpr
    @64
    @73
    @17
    @64
    @72
    vz
    @1
    @64
    @9
    @1
    wcel
    #
    wa
    #
    @15
    @68
    @75
    @15
    wa
    @68
    @74
    @13
    @4
    wcel
    #
    @64
    @74
    @15
    simplr
    @64
    @15
    @76
    @74
    @64
    @15
    wa
    @53
    @4
    @13
    @56
    @54
    @63
    @15
    simpllr
    @64
    @13
    @53
    wcel
    #
    @15
    @64
    @14
    wrel
    #
    @77
    @15
    wb
    @64
    @25
    @55
    @78
    wph
    @25
    @40
    @50
    @55
    @54
    @63
    @37
    ad5antr
    @51
    @55
    @54
    @63
    simpllr
    @20
    @14
    @2
    ustrel
    syl2anc
    @12
    @13
    @14
    elrelimasn
    syl
    biimpar
    sseldd
    adantlr
    wph
    @68
    @74
    @76
    wa
    wb
    #
    @40
    @50
    @55
    @54
    @63
    @74
    @15
    wph
    @3
    cF
    @1
    wfn
    #
    @79
    @39
    @1
    @2
    cF
    ffn
    #
    @1
    @9
    @4
    cF
    elpreima
    3syl
    ad7antr
    mpbir2and
    ex
    ralrimiva
    adantr
    @17
    @73
    wa
    @16
    @72
    wa
    #
    vz
    @1
    wral
    @70
    @16
    @72
    vz
    @1
    r19.26
    @82
    @69
    vz
    @1
    @11
    @15
    @68
    pm3.33
    ralimi
    sylbir
    syl2anc
    wph
    @66
    @67
    wa
    #
    @70
    w3a
    #
    vy
    @43
    @5
    @84
    vy
    cv
    #
    @43
    wcel
    #
    @85
    @5
    wcel
    #
    @84
    @86
    wa
    #
    @8
    @85
    @10
    wbr
    #
    @87
    @88
    @66
    @86
    @89
    @66
    @67
    wph
    @70
    @86
    simpl2l
    @84
    @86
    simpr
    #
    @66
    @86
    @89
    @8
    @85
    @10
    elrelimasn
    biimpa
    syl2anc
    @88
    @85
    @1
    wcel
    @70
    @89
    @87
    wi
    #
    @88
    @43
    @1
    @85
    @66
    @67
    wph
    @70
    @86
    simpl2r
    @90
    sseldd
    wph
    @83
    @70
    @86
    simpl3
    @69
    @91
    vz
    @85
    @1
    @9
    @85
    wceq
    @11
    @89
    @68
    @87
    @9
    @85
    @8
    @10
    breq2
    @9
    @85
    @5
    eleq1
    imbi12d
    rspcv
    sylc
    mpd
    ex
    ssrdv
    syl121anc
    ex
    reximdva
    mpd
    @51
    @12
    @4
    wcel
    #
    @14
    @85
    csn
    #
    cima
    #
    @4
    wss
    #
    vs
    @20
    wrex
    #
    vy
    @4
    wral
    #
    @54
    vs
    @20
    wrex
    #
    @51
    @59
    @92
    @41
    @50
    @59
    @92
    wa
    #
    wph
    @50
    @99
    wb
    #
    @40
    wph
    @3
    @80
    @100
    @39
    @81
    @1
    @8
    @4
    cF
    elpreima
    3syl
    adantr
    biimpa
    simprd
    @41
    @97
    @50
    @41
    @4
    @2
    wss
    #
    @97
    @41
    @4
    @33
    wcel
    #
    @101
    @97
    wa
    #
    @41
    @4
    cK
    @33
    wph
    @40
    simpr
    wph
    @34
    @40
    wph
    @32
    @34
    ucncn.2
    @32
    @25
    @34
    @36
    simprbi
    syl
    adantr
    eleqtrd
    wph
    @102
    @103
    wb
    #
    @40
    wph
    @25
    @104
    @37
    vy
    vs
    @4
    @20
    @2
    elutop
    syl
    adantr
    mpbid
    simprd
    adantr
    @96
    @98
    vy
    @12
    @4
    @85
    @12
    wceq
    #
    @95
    @54
    vs
    @20
    @105
    @94
    @53
    @4
    @105
    @93
    @52
    @14
    @85
    @12
    sneq
    imaeq2d
    sseq1d
    rexbidv
    rspcv
    sylc
    r19.29a
    ralrimiva
    @41
    @6
    @5
    @27
    wcel
    #
    @42
    @46
    wa
    #
    @41
    cJ
    @27
    @5
    wph
    @28
    @40
    wph
    @26
    @28
    ucncn.1
    @26
    @24
    @28
    @30
    simprbi
    syl
    adantr
    eleq2d
    wph
    @106
    @107
    wb
    #
    @40
    wph
    @24
    @108
    @31
    vx
    vr
    @5
    @18
    @1
    elutop
    syl
    adantr
    bitrd
    mpbir2and
    ralrimiva
    wph
    cJ
    @1
    ctopon
    cfv
    wcel
    #
    cK
    @2
    ctopon
    cfv
    wcel
    #
    @0
    @3
    @7
    wa
    wb
    wph
    cR
    ctps
    wcel
    @109
    ucncn.3
    @1
    cJ
    cR
    @29
    ucncn.j
    istps
    sylib
    wph
    cS
    ctps
    wcel
    @110
    ucncn.4
    @2
    cK
    cS
    @35
    ucncn.k
    istps
    sylib
    va
    cF
    cJ
    cK
    @1
    @2
    iscn
    syl2anc
    mpbir2and
end
