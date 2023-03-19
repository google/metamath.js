include "cv.mm"
include "cfv.mm"
include "ciin.mm"
include "cli.mm"
include "wbr.mm"
include "cmpt.mm"
include "cmin.mm"
include "co.mm"
include "cuz.mm"
include "wcel.mm"
include "wa.mm"
include "cdif.mm"
include "wceq.mm"
include "wss.mm"
include "uzss.mm"
include "syl.mm"
include "syl6sseqr.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "cvv.mm"
include "a1i.mm"
include "cdm.mm"
include "csalg.mm"
include "eqid.mm"
include "dmmeasal.mm"
include "syl6eleqr.mm"
include "ffvelrnda.mm"
include "mpdan.mm"
include "saldifcl2.mm"
include "syl3anc.mm"
include "elexd.mm"
include "fvmpt2d.mm"
include "syldan.mm"
include "fveq2d.mm"
include "cmea.mm"
include "cr.mm"
include "cfzo.mm"
include "c1.mm"
include "caddc.mm"
include "simpl.mm"
include "elfzouz.mm"
include "adantl.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "oveq1.mm"
include "fveq2.mm"
include "sseq12d.mm"
include "imbi12d.mm"
include "chvarv.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "ssdec.mm"
include "meadif.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "cc.mm"
include "recnd.mm"
include "meassre.mm"
include "nncand.mm"
include "eqtr2d.mm"
include "mpteq2dva.mm"
include "nfv.mm"
include "eluzelzd.mm"
include "difssd.mm"
include "eqsstrd.mm"
include "fmptd.mm"
include "ciun.mm"
include "sscond.mm"
include "difeq2d.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "peano2uzs.mm"
include "fvex.mm"
include "difexi.mm"
include "fvmptd.mm"
include "mpbird.mm"
include "meassle.mm"
include "meaiuninc2.mm"
include "climresmpt.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "breqtrd.mm"
include "climsubc1mpt.mm"
include "eqbrtrd.mm"
include "mpbid.mm"
include "cun.mm"
include "eqidd.mm"
include "com.mm"
include "cdom.mm"
include "uzct.mm"
include "saliuncl.mm"
include "syl5eqel.mm"
include "cin.mm"
include "c0.mm"
include "disjdif.mm"
include "iunssd.mm"
include "syl5eqss.mm"
include "meadjunre.mm"
include "undif.mm"
include "sylib.mm"
include "3eqtr3d.mm"
include "subaddd.mm"
include "wral.mm"
include "wn.mm"
include "simpllr.mm"
include "wrex.mm"
include "simplr.mm"
include "eldifi.mm"
include "ad2antrr.mm"
include "eldifd.mm"
include "rspe.mm"
include "eliun.mm"
include "sylibr.mm"
include "adantlll.mm"
include "iuneq2dv.mm"
include "eqcomd.mm"
include "ad3antrrr.mm"
include "eleqtrd.mm"
include "elndif.mm"
include "condan.mm"
include "ralrimiva.mm"
include "wb.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "ssd.mm"
include "ssid.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "iinss.mm"
include "nfcv.mm"
include "nfii1.mm"
include "nfel.mm"
include "iinss2.mm"
include "ex.mm"
include "ralrimi.mm"
include "ralnex.mm"
include "sylnibr.mm"
include "neleqtrrd.mm"
include "eqssd.mm"
include "breq12d.mm"

theorem meaiininclem
  let wph: wff ph
  let cS: class S
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cK: class K
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vm: setvar m
  let vx: setvar x
  let vk: setvar k
  assume meaiininclem.m: |- ( ph -> M e. Meas )
  assume meaiininclem.n: |- ( ph -> N e. ZZ )
  assume meaiininclem.z: |- Z = ( ZZ>= ` N )
  assume meaiininclem.e: |- ( ph -> E : Z --> dom M )
  assume meaiininclem.i: |- ( ( ph /\ n e. Z ) -> ( E ` ( n + 1 ) ) C_ ( E ` n ) )
  assume meaiininclem.k: |- ( ph -> K e. ( ZZ>= ` N ) )
  assume meaiininclem.r: |- ( ph -> ( M ` ( E ` K ) ) e. RR )
  assume meaiininclem.s: |- S = ( n e. Z |-> ( M ` ( E ` n ) ) )
  assume meaiininclem.g: |- G = ( n e. Z |-> ( ( E ` K ) \ ( E ` n ) ) )
  assume meaiininclem.f: |- F = U_ n e. Z ( G ` n )

  disjoint E n
  disjoint F n
  disjoint G n
  disjoint K n
  disjoint M n
  disjoint N n
  disjoint Z n
  disjoint n ph
  disjoint E m
  disjoint m n
  disjoint E x
  disjoint n x
  disjoint F x
  disjoint K m
  disjoint K x
  disjoint Z m
  disjoint Z x
  disjoint m ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> S ~~> ( M ` |^|_ n e. Z ( E ` n ) ) )

  proof
    wph
    cS
    vn
    cZ
    vn
    cv
    #
    cE
    cfv
    #
    ciin
    #
    cM
    cfv
    #
    cli
    wbr
    vn
    cZ
    @1
    cM
    cfv
    #
    cmpt
    #
    cK
    cE
    cfv
    #
    cM
    cfv
    #
    cF
    cM
    cfv
    #
    cmin
    co
    #
    cli
    wbr
    #
    wph
    vn
    cK
    cuz
    cfv
    #
    @4
    cmpt
    #
    @9
    cli
    wbr
    @10
    wph
    @12
    vn
    @11
    @7
    @0
    cG
    cfv
    #
    cM
    cfv
    #
    cmin
    co
    #
    cmpt
    @9
    cli
    wph
    vn
    @11
    @4
    @15
    wph
    @0
    @11
    wcel
    #
    wa
    #
    @15
    @7
    @7
    @4
    cmin
    co
    #
    cmin
    co
    @4
    @17
    @14
    @18
    @7
    cmin
    @17
    @14
    @6
    @1
    cdif
    #
    cM
    cfv
    @18
    @17
    @13
    @19
    cM
    wph
    @16
    @0
    cZ
    wcel
    #
    @13
    @19
    wceq
    @17
    @11
    cZ
    @0
    wph
    @11
    cZ
    wss
    #
    @16
    wph
    @11
    cN
    cuz
    cfv
    #
    cZ
    wph
    cK
    @22
    wcel
    @11
    @22
    wss
    meaiininclem.k
    cN
    cK
    uzss
    syl
    meaiininclem.z
    syl6sseqr
    #
    adantr
    wph
    @16
    simpr
    #
    sseldd
    #
    wph
    vn
    cZ
    @19
    cG
    cvv
    cG
    vn
    cZ
    @19
    cmpt
    #
    wceq
    wph
    meaiininclem.g
    a1i
    wph
    @20
    wa
    #
    @19
    cM
    cdm
    #
    @27
    @28
    csalg
    wcel
    #
    @6
    @28
    wcel
    #
    @1
    @28
    wcel
    #
    @19
    @28
    wcel
    wph
    @29
    @20
    wph
    @28
    cM
    meaiininclem.m
    @28
    eqid
    #
    dmmeasal
    #
    adantr
    wph
    @30
    @20
    wph
    cK
    cZ
    wcel
    #
    @30
    wph
    cK
    @22
    cZ
    meaiininclem.k
    meaiininclem.z
    syl6eleqr
    #
    wph
    cZ
    @28
    cK
    cE
    meaiininclem.e
    ffvelrnda
    mpdan
    #
    adantr
    #
    wph
    cZ
    @28
    @0
    cE
    meaiininclem.e
    ffvelrnda
    #
    @28
    @6
    @1
    saldifcl2
    syl3anc
    #
    elexd
    fvmpt2d
    #
    syldan
    fveq2d
    @17
    @6
    @1
    cM
    wph
    cM
    cmea
    wcel
    #
    @16
    meaiininclem.m
    adantr
    #
    wph
    @30
    @16
    @36
    adantr
    #
    wph
    @7
    cr
    wcel
    @16
    meaiininclem.r
    adantr
    #
    wph
    @16
    @20
    @31
    @25
    @38
    syldan
    #
    @17
    vm
    cE
    cK
    @0
    @24
    wph
    vm
    cv
    #
    cK
    @0
    cfzo
    co
    wcel
    #
    @46
    c1
    caddc
    co
    #
    cE
    cfv
    #
    @46
    cE
    cfv
    #
    wss
    #
    @16
    wph
    @47
    wa
    #
    wph
    @46
    cZ
    wcel
    #
    @51
    wph
    @47
    simpl
    #
    @52
    @11
    cZ
    @46
    @52
    wph
    @21
    @54
    @23
    syl
    @47
    @46
    @11
    wcel
    wph
    @46
    cK
    @0
    elfzouz
    adantl
    sseldd
    @27
    @0
    c1
    caddc
    co
    #
    cE
    cfv
    #
    @1
    wss
    #
    wi
    wph
    @53
    wa
    #
    @51
    wi
    vn
    vm
    @0
    @46
    wceq
    #
    @27
    @58
    @57
    @51
    @59
    @20
    @53
    wph
    @0
    @46
    cZ
    eleq1
    anbi2d
    @59
    @56
    @49
    @1
    @50
    @59
    @55
    @48
    cE
    @0
    @46
    c1
    caddc
    oveq1
    fveq2d
    @0
    @46
    cE
    fveq2
    #
    sseq12d
    imbi12d
    meaiininclem.i
    chvarv
    syl2anc
    adantlr
    ssdec
    #
    meadif
    eqtrd
    oveq2d
    @17
    @7
    @4
    wph
    @7
    cc
    wcel
    @16
    wph
    @7
    meaiininclem.r
    recnd
    #
    adantr
    @17
    @4
    @17
    @6
    @1
    cM
    @42
    @43
    @44
    @61
    @45
    meassre
    recnd
    nncand
    eqtr2d
    mpteq2dva
    wph
    @7
    @14
    @8
    vn
    cK
    @11
    wph
    vn
    nfv
    @11
    eqid
    wph
    cN
    cK
    meaiininclem.k
    eluzelzd
    @62
    @17
    @14
    @17
    @6
    @13
    cM
    @42
    @43
    @44
    wph
    @16
    @20
    @13
    @6
    wss
    @25
    @27
    @13
    @19
    @6
    @40
    @27
    @6
    @1
    difssd
    eqsstrd
    #
    syldan
    wph
    @16
    @20
    @13
    @28
    wcel
    @25
    wph
    cZ
    @28
    @0
    cG
    wph
    vn
    cZ
    @19
    @28
    cG
    @39
    meaiininclem.g
    fmptd
    #
    ffvelrnda
    #
    syldan
    meassre
    recnd
    wph
    vn
    @11
    @14
    cmpt
    #
    vn
    cZ
    @13
    ciun
    #
    cM
    cfv
    #
    @8
    cli
    wph
    @66
    @68
    cli
    wbr
    vn
    cZ
    @14
    cmpt
    #
    @68
    cli
    wbr
    wph
    @7
    @69
    vn
    cG
    cM
    cN
    cZ
    meaiininclem.m
    meaiininclem.n
    meaiininclem.z
    @64
    @27
    @13
    @55
    cG
    cfv
    #
    wss
    @19
    @6
    @56
    cdif
    #
    wss
    @27
    @56
    @1
    @6
    meaiininclem.i
    sscond
    @27
    @13
    @19
    @70
    @71
    @40
    @27
    vm
    @55
    @6
    @50
    cdif
    #
    @71
    cZ
    cG
    cvv
    cG
    vm
    cZ
    @72
    cmpt
    #
    wceq
    @27
    cG
    @26
    @73
    meaiininclem.g
    vn
    vm
    cZ
    @19
    @72
    @59
    @1
    @50
    @6
    @60
    difeq2d
    cbvmptv
    eqtri
    a1i
    @46
    @55
    wceq
    #
    @72
    @71
    wceq
    @27
    @74
    @50
    @56
    @6
    @46
    @55
    cE
    fveq2
    difeq2d
    adantl
    @20
    @55
    cZ
    wcel
    wph
    cN
    @0
    cZ
    meaiininclem.z
    peano2uzs
    adantl
    @71
    cvv
    wcel
    @27
    @6
    @56
    cK
    cE
    fvex
    difexi
    a1i
    fvmptd
    sseq12d
    mpbird
    meaiininclem.r
    @27
    @13
    @6
    @28
    cM
    wph
    @41
    @20
    meaiininclem.m
    adantr
    @32
    @65
    @37
    @63
    meassle
    @69
    eqid
    #
    meaiuninc2
    wph
    vn
    @14
    @68
    @69
    @66
    cN
    cK
    cZ
    meaiininclem.z
    @75
    @35
    @66
    eqid
    climresmpt
    mpbird
    @68
    @8
    wceq
    wph
    @67
    cF
    cM
    cF
    @67
    meaiininclem.f
    eqcomi
    fveq2i
    a1i
    breqtrd
    climsubc1mpt
    eqbrtrd
    wph
    vn
    @4
    @9
    @5
    @12
    cN
    cK
    cZ
    meaiininclem.z
    @5
    eqid
    @35
    @12
    eqid
    climresmpt
    mpbid
    wph
    cS
    @5
    @3
    @9
    cli
    cS
    @5
    wceq
    wph
    meaiininclem.s
    a1i
    wph
    @9
    @6
    cF
    cdif
    #
    cM
    cfv
    #
    @3
    wph
    @9
    @77
    wceq
    @8
    @77
    caddc
    co
    #
    @7
    wceq
    wph
    cF
    @76
    cun
    #
    cM
    cfv
    #
    @80
    @78
    @7
    wph
    @80
    eqidd
    wph
    cF
    @76
    @28
    cM
    meaiininclem.m
    @32
    wph
    cF
    @67
    @28
    meaiininclem.f
    wph
    @28
    vn
    @13
    cZ
    @33
    cZ
    com
    cdom
    wbr
    wph
    cN
    cZ
    meaiininclem.z
    uzct
    a1i
    @65
    saliuncl
    syl5eqel
    #
    wph
    @29
    @30
    cF
    @28
    wcel
    @76
    @28
    wcel
    @33
    @36
    @81
    @28
    @6
    cF
    saldifcl2
    syl3anc
    #
    cF
    @76
    cin
    c0
    wceq
    wph
    cF
    @6
    disjdif
    a1i
    wph
    @6
    cF
    cM
    meaiininclem.m
    @36
    meaiininclem.r
    wph
    cF
    @67
    @6
    meaiininclem.f
    wph
    vn
    cZ
    @13
    @6
    @63
    iunssd
    syl5eqss
    #
    @81
    meassre
    #
    wph
    @6
    @76
    cM
    meaiininclem.m
    @36
    meaiininclem.r
    wph
    @6
    cF
    difssd
    @82
    meassre
    #
    meadjunre
    wph
    @79
    @6
    cM
    wph
    cF
    @6
    wss
    @79
    @6
    wceq
    @83
    cF
    @6
    undif
    sylib
    fveq2d
    3eqtr3d
    wph
    @7
    @8
    @77
    @62
    wph
    @8
    @84
    recnd
    wph
    @77
    @85
    recnd
    subaddd
    mpbird
    wph
    @76
    @2
    cM
    wph
    @76
    @2
    wph
    vx
    @76
    @2
    wph
    vx
    cv
    #
    @76
    wcel
    #
    wa
    #
    @86
    @1
    wcel
    #
    vn
    cZ
    wral
    #
    @86
    @2
    wcel
    #
    @88
    @89
    vn
    cZ
    @88
    @20
    wa
    #
    @89
    @87
    wph
    @87
    @20
    @89
    wn
    #
    simpllr
    @92
    @93
    wa
    #
    @86
    cF
    wcel
    @87
    wn
    @94
    @86
    vn
    cZ
    @19
    ciun
    #
    cF
    @87
    @20
    @93
    @86
    @95
    wcel
    #
    wph
    @87
    @20
    wa
    #
    @93
    wa
    #
    @86
    @19
    wcel
    #
    vn
    cZ
    wrex
    #
    @96
    @98
    @20
    @99
    @100
    @87
    @20
    @93
    simplr
    @98
    @86
    @6
    @1
    @87
    @86
    @6
    wcel
    @20
    @93
    @86
    @6
    cF
    eldifi
    ad2antrr
    @97
    @93
    simpr
    eldifd
    @99
    vn
    cZ
    rspe
    syl2anc
    vn
    @86
    cZ
    @19
    eliun
    #
    sylibr
    adantlll
    wph
    @95
    cF
    wceq
    @87
    @20
    @93
    wph
    cF
    @95
    wph
    cF
    @67
    @95
    cF
    @67
    wceq
    wph
    meaiininclem.f
    a1i
    wph
    vn
    cZ
    @13
    @19
    @40
    iuneq2dv
    eqtrd
    #
    eqcomd
    ad3antrrr
    eleqtrd
    @86
    cF
    @6
    elndif
    syl
    condan
    ralrimiva
    @86
    cvv
    wcel
    @91
    @90
    wb
    vx
    vex
    vn
    @86
    cZ
    @1
    cvv
    eliin
    ax-mp
    sylibr
    ssd
    wph
    vx
    @2
    @76
    wph
    @91
    wa
    #
    @86
    @6
    cF
    @103
    @2
    @6
    @86
    wph
    @2
    @6
    wss
    #
    @91
    wph
    @1
    @6
    wss
    #
    vn
    cZ
    wrex
    #
    @104
    wph
    @34
    @6
    @6
    wss
    #
    @106
    @35
    @107
    wph
    @6
    ssid
    a1i
    @105
    @107
    vn
    cK
    cZ
    @0
    cK
    wceq
    @1
    @6
    @6
    @0
    cK
    cE
    fveq2
    sseq1d
    rspcev
    syl2anc
    vn
    cZ
    @1
    @6
    iinss
    syl
    adantr
    wph
    @91
    simpr
    sseldd
    @103
    cF
    @95
    @86
    @91
    @96
    wn
    wph
    @91
    @100
    @96
    @91
    @99
    wn
    #
    vn
    cZ
    wral
    @100
    wn
    @91
    @108
    vn
    cZ
    vn
    @86
    @2
    vn
    @86
    nfcv
    vn
    cZ
    @1
    nfii1
    nfel
    @91
    @20
    @108
    @91
    @20
    wa
    #
    @89
    @108
    @109
    @2
    @1
    @86
    @20
    @2
    @1
    wss
    @91
    vn
    cZ
    @1
    iinss2
    adantl
    @91
    @20
    simpl
    sseldd
    @86
    @1
    @6
    elndif
    syl
    ex
    ralrimi
    @99
    vn
    cZ
    ralnex
    sylib
    @101
    sylnibr
    adantl
    wph
    cF
    @95
    wceq
    @91
    @102
    adantr
    neleqtrrd
    eldifd
    ssd
    eqssd
    fveq2d
    eqtr2d
    breq12d
    mpbird
end
