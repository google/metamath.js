include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cfv.mm"
include "ciun.mm"
include "wceq.mm"
include "wral.mm"
include "wdisj.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "eliun.mm"
include "biimpi.mm"
include "adantl.mm"
include "wi.mm"
include "nfcv.mm"
include "nfiu1.mm"
include "nfel.mm"
include "w3a.mm"
include "simp2.mm"
include "simpl.mm"
include "cuz.mm"
include "elfzuz.mm"
include "eqcomi.mm"
include "syl6eleq.mm"
include "cfzo.mm"
include "cdif.mm"
include "cvv.mm"
include "simpr.mm"
include "ffvelrnda.mm"
include "difexg.mm"
include "syl.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "difssd.mm"
include "eqsstrd.mm"
include "3adant3.mm"
include "simp3.mm"
include "sseldd.mm"
include "rspe.mm"
include "sylibr.mm"
include "3exp.mm"
include "rexlimd.mm"
include "adantr.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "fzssuz.mm"
include "a1i.mm"
include "nfv.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "uzwo4.mm"
include "simprl.mm"
include "nfra1.mm"
include "nfan.mm"
include "c1.mm"
include "cmin.mm"
include "cr.mm"
include "elfzoelz.mm"
include "zred.mm"
include "elfzelz.mm"
include "1red.mm"
include "resubcld.mm"
include "cle.mm"
include "elfzolem1.mm"
include "ltm1d.mm"
include "lelttrd.mm"
include "ad4ant24.mm"
include "simplr.mm"
include "cz.mm"
include "elfzel1.mm"
include "elfzel2.mm"
include "3jca.mm"
include "elfzole1.mm"
include "elfzle2.mm"
include "ltletrd.mm"
include "ltled.mm"
include "jca32.mm"
include "elfz2.mm"
include "adantlr.mm"
include "rspa.mm"
include "adantlll.mm"
include "ex.mm"
include "ralrimi.mm"
include "ralnex.mm"
include "sylib.mm"
include "sylnibr.mm"
include "adantrl.mm"
include "eldifd.mm"
include "syldan.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "reximdai.mm"
include "eqssd.mm"
include "ralrimivw.mm"
include "iuneqfzuz.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "cmpt.mm"
include "oveq2.mm"
include "iuneq1d.mm"
include "difeq12d.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "simpllr.mm"
include "iundjiunlem.mm"
include "simpll.mm"
include "wne.mm"
include "neqne.mm"
include "id.mm"
include "eluzelz.mm"
include "ad2antrr.mm"
include "ad3antrrr.mm"
include "lenltd.mm"
include "mpbird.mm"
include "leneltd.mm"
include "sylanl2.mm"
include "ad5ant2345.mm"
include "anass.mm"
include "incom.mm"
include "simplrr.mm"
include "simplrl.mm"
include "eqtrd.mm"
include "sylanb.mm"
include "pm2.61dan.mm"
include "df-or.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "cbvdisj.mm"
include "disjor.mm"
include "nfin.mm"
include "nfeq.mm"
include "nfor.mm"
include "nfral.mm"
include "equequ1.mm"
include "ineq1d.mm"
include "eqeq1d.mm"
include "orbi12d.mm"
include "ralbidv.mm"
include "cbvral.mm"
include "3bitri.mm"
include "jca31.mm"

theorem iundjiun
  let wph: wff ph
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cN: class N
  let cV: class V
  let cZ: class Z
  let vx: setvar x
  let vk: setvar k
  assume iundjiun.nph: |- F/ n ph
  assume iundjiun.z: |- Z = ( ZZ>= ` N )
  assume iundjiun.e: |- ( ph -> E : Z --> V )
  assume iundjiun.f: |- F = ( n e. Z |-> ( ( E ` n ) \ U_ i e. ( N ..^ n ) ( E ` i ) ) )

  disjoint E i
  disjoint E m
  disjoint E n
  disjoint i m
  disjoint i n
  disjoint m n
  disjoint F m
  disjoint N i
  disjoint N m
  disjoint N n
  disjoint Z m
  disjoint Z n
  disjoint i ph
  disjoint m ph
  disjoint E x
  disjoint i x
  disjoint m x
  disjoint n x
  disjoint F k
  disjoint k m
  disjoint F x
  disjoint N x
  disjoint Z k
  disjoint k n
  disjoint i k
  disjoint k ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( A. m e. Z U_ n e. ( N ... m ) ( F ` n ) = U_ n e. ( N ... m ) ( E ` n ) /\ U_ n e. Z ( F ` n ) = U_ n e. Z ( E ` n ) ) /\ Disj_ n e. Z ( F ` n ) ) )

  proof
    wph
    vn
    cN
    vm
    cv
    #
    cfz
    co
    #
    vn
    cv
    #
    cF
    cfv
    #
    ciun
    #
    vn
    @1
    @2
    cE
    cfv
    #
    ciun
    #
    wceq
    #
    vm
    cZ
    wral
    #
    vn
    cZ
    @3
    ciun
    vn
    cZ
    @5
    ciun
    wceq
    #
    vn
    cZ
    @3
    wdisj
    #
    wph
    @7
    vm
    cZ
    wph
    @4
    @6
    wph
    vx
    cv
    #
    @6
    wcel
    #
    vx
    @4
    wral
    @4
    @6
    wss
    wph
    @12
    vx
    @4
    wph
    @11
    @4
    wcel
    #
    wa
    @11
    @3
    wcel
    #
    vn
    @1
    wrex
    #
    @12
    @13
    @15
    wph
    @13
    @15
    vn
    @11
    @1
    @3
    eliun
    #
    biimpi
    adantl
    wph
    @15
    @12
    wi
    @13
    wph
    @14
    @12
    vn
    @1
    iundjiun.nph
    vn
    @11
    @6
    vn
    @11
    nfcv
    vn
    @1
    @5
    nfiu1
    nfel
    wph
    @2
    @1
    wcel
    #
    @14
    @12
    wph
    @17
    @14
    w3a
    #
    @11
    @5
    wcel
    #
    vn
    @1
    wrex
    #
    @12
    @18
    @17
    @19
    @20
    wph
    @17
    @14
    simp2
    @18
    @3
    @5
    @11
    wph
    @17
    @3
    @5
    wss
    #
    @14
    wph
    @17
    wa
    #
    wph
    @2
    cZ
    wcel
    #
    @21
    wph
    @17
    simpl
    @17
    @23
    wph
    @17
    @2
    cN
    cuz
    cfv
    #
    cZ
    @2
    cN
    @0
    elfzuz
    cZ
    @24
    iundjiun.z
    eqcomi
    syl6eleq
    adantl
    #
    wph
    @23
    wa
    #
    @3
    @5
    vi
    cN
    @2
    cfzo
    co
    #
    vi
    cv
    #
    cE
    cfv
    #
    ciun
    #
    cdif
    #
    @5
    @26
    @23
    @31
    cvv
    wcel
    #
    @3
    @31
    wceq
    #
    wph
    @23
    simpr
    @26
    @5
    cV
    wcel
    @32
    wph
    cZ
    cV
    @2
    cE
    iundjiun.e
    ffvelrnda
    @5
    @30
    cV
    difexg
    syl
    vn
    cZ
    @31
    cvv
    cF
    iundjiun.f
    fvmpt2
    syl2anc
    #
    @26
    @5
    @30
    difssd
    eqsstrd
    syl2anc
    3adant3
    wph
    @17
    @14
    simp3
    sseldd
    @19
    vn
    @1
    rspe
    syl2anc
    vn
    @11
    @1
    @5
    eliun
    #
    sylibr
    3exp
    rexlimd
    adantr
    mpd
    ralrimiva
    vx
    @4
    @6
    dfss3
    sylibr
    wph
    @13
    vx
    @6
    wral
    @6
    @4
    wss
    wph
    @13
    vx
    @6
    wph
    @12
    wa
    #
    @15
    @13
    @36
    @19
    @28
    @2
    clt
    wbr
    #
    @11
    @29
    wcel
    #
    wn
    #
    wi
    #
    vi
    @1
    wral
    #
    wa
    #
    vn
    @1
    wrex
    #
    @15
    @12
    @43
    wph
    @12
    @1
    @24
    wss
    #
    @20
    @43
    @44
    @12
    cN
    @0
    fzssuz
    a1i
    @12
    @20
    @35
    biimpi
    @19
    @38
    @1
    vn
    vi
    cN
    @38
    vn
    nfv
    @2
    @28
    wceq
    @5
    @29
    @11
    @2
    @28
    cE
    fveq2
    eleq2d
    uzwo4
    syl2anc
    adantl
    wph
    @43
    @15
    wi
    @12
    wph
    @42
    @14
    vn
    @1
    iundjiun.nph
    wph
    @17
    @42
    @14
    wi
    @22
    @42
    @14
    @22
    @42
    wa
    #
    @11
    @31
    @3
    @45
    @11
    @5
    @30
    @22
    @19
    @41
    simprl
    @22
    @41
    @11
    @30
    wcel
    #
    wn
    @19
    @22
    @41
    wa
    #
    @38
    vi
    @27
    wrex
    #
    @46
    @47
    @39
    vi
    @27
    wral
    @48
    wn
    @47
    @39
    vi
    @27
    @22
    @41
    vi
    @22
    vi
    nfv
    @40
    vi
    @1
    nfra1
    nfan
    @47
    @28
    @27
    wcel
    #
    @39
    @47
    @49
    wa
    @37
    @39
    @17
    @49
    @37
    wph
    @41
    @17
    @49
    wa
    #
    @28
    @2
    c1
    cmin
    co
    #
    @2
    @49
    @28
    cr
    wcel
    @17
    @49
    @28
    @28
    cN
    @2
    elfzoelz
    #
    zred
    adantl
    #
    @50
    @2
    c1
    @17
    @2
    cr
    wcel
    #
    @49
    @17
    @2
    @2
    cN
    @0
    elfzelz
    zred
    #
    adantr
    #
    @50
    1red
    resubcld
    #
    @56
    @49
    @28
    @51
    cle
    wbr
    @17
    @28
    cN
    @2
    elfzolem1
    adantl
    #
    @50
    @2
    @56
    ltm1d
    lelttrd
    ad4ant24
    @17
    @41
    @49
    @40
    wph
    @17
    @41
    wa
    @49
    wa
    @41
    @28
    @1
    wcel
    #
    @40
    @17
    @41
    @49
    simplr
    @17
    @49
    @59
    @41
    @50
    cN
    cz
    wcel
    #
    @0
    cz
    wcel
    #
    @28
    cz
    wcel
    #
    w3a
    #
    cN
    @28
    cle
    wbr
    #
    @28
    @0
    cle
    wbr
    #
    wa
    wa
    @59
    @50
    @63
    @64
    @65
    @50
    @60
    @61
    @62
    @17
    @60
    @49
    @2
    cN
    @0
    elfzel1
    adantr
    @17
    @61
    @49
    @2
    cN
    @0
    elfzel2
    #
    adantr
    #
    @49
    @62
    @17
    @52
    adantl
    3jca
    @49
    @64
    @17
    @28
    cN
    @2
    elfzole1
    adantl
    @50
    @28
    @0
    @53
    @50
    @0
    @67
    zred
    #
    @50
    @28
    @51
    @0
    @53
    @57
    @68
    @58
    @17
    @51
    @0
    clt
    wbr
    @49
    @17
    @51
    @2
    @0
    @17
    @2
    c1
    @55
    @17
    1red
    resubcld
    @55
    @17
    @0
    @66
    zred
    @17
    @2
    @55
    ltm1d
    @2
    cN
    @0
    elfzle2
    ltletrd
    adantr
    lelttrd
    ltled
    jca32
    @28
    cN
    @0
    elfz2
    sylibr
    adantlr
    @40
    vi
    @1
    rspa
    syl2anc
    adantlll
    mpd
    ex
    ralrimi
    @38
    vi
    @27
    ralnex
    sylib
    vi
    @11
    @27
    @29
    eliun
    sylnibr
    adantrl
    eldifd
    @22
    @31
    @3
    wceq
    @42
    @22
    @3
    @31
    wph
    @17
    @23
    @33
    @25
    @34
    syldan
    eqcomd
    adantr
    eleqtrd
    ex
    ex
    reximdai
    adantr
    mpd
    @16
    sylibr
    ralrimiva
    vx
    @6
    @4
    dfss3
    sylibr
    eqssd
    ralrimivw
    #
    wph
    @8
    @9
    @69
    @3
    @5
    vm
    vn
    cN
    cZ
    iundjiun.z
    iuneqfzuz
    syl
    wph
    @2
    vk
    cv
    #
    wceq
    #
    @3
    @70
    cF
    cfv
    #
    cin
    #
    c0
    wceq
    #
    wo
    #
    vk
    cZ
    wral
    #
    vn
    cZ
    wral
    #
    @10
    wph
    @76
    vn
    cZ
    iundjiun.nph
    wph
    @23
    @76
    @26
    @75
    vk
    cZ
    @26
    @70
    cZ
    wcel
    #
    wa
    #
    @71
    wn
    #
    @74
    wi
    @75
    @79
    @80
    @74
    @79
    @80
    wa
    #
    @2
    @70
    clt
    wbr
    #
    @74
    @79
    @82
    @74
    @80
    @79
    @82
    wa
    vi
    vm
    cE
    cF
    @2
    @70
    cN
    cZ
    iundjiun.z
    cF
    vn
    cZ
    @31
    cmpt
    #
    vm
    cZ
    @0
    cE
    cfv
    #
    vi
    cN
    @0
    cfzo
    co
    #
    @29
    ciun
    #
    cdif
    #
    cmpt
    iundjiun.f
    vn
    vm
    cZ
    @31
    @87
    @2
    @0
    wceq
    #
    @5
    @84
    @30
    @86
    @2
    @0
    cE
    fveq2
    @88
    vi
    @27
    @85
    @29
    @2
    @0
    cN
    cfzo
    oveq2
    iuneq1d
    difeq12d
    cbvmptv
    eqtri
    #
    wph
    @23
    @78
    @82
    simpllr
    @26
    @78
    @82
    simplr
    @79
    @82
    simpr
    iundjiunlem
    adantlr
    @81
    @82
    wn
    #
    wa
    @79
    @70
    @2
    clt
    wbr
    #
    @74
    @79
    @80
    @90
    simpll
    @23
    @78
    @80
    @90
    @91
    wph
    @80
    @23
    @78
    wa
    #
    @2
    @70
    wne
    #
    @90
    @91
    @2
    @70
    neqne
    @92
    @93
    wa
    @90
    wa
    @70
    @2
    @92
    @70
    cr
    wcel
    #
    @93
    @90
    @78
    @94
    @23
    @78
    @70
    @78
    @70
    @24
    wcel
    @70
    cz
    wcel
    @78
    @70
    cZ
    @24
    @78
    id
    iundjiun.z
    syl6eleq
    cN
    @70
    eluzelz
    syl
    zred
    adantl
    #
    ad2antrr
    @23
    @54
    @78
    @93
    @90
    @23
    @2
    @23
    @2
    @24
    wcel
    @2
    cz
    wcel
    @23
    @2
    cZ
    @24
    @23
    id
    iundjiun.z
    syl6eleq
    cN
    @2
    eluzelz
    syl
    zred
    #
    ad3antrrr
    @92
    @90
    @70
    @2
    cle
    wbr
    #
    @93
    @92
    @90
    wa
    #
    @97
    @90
    @92
    @90
    simpr
    @98
    @70
    @2
    @92
    @94
    @90
    @95
    adantr
    @23
    @54
    @78
    @90
    @96
    ad2antrr
    lenltd
    mpbird
    adantlr
    @92
    @93
    @90
    simplr
    leneltd
    sylanl2
    ad5ant2345
    @79
    wph
    @92
    wa
    #
    @91
    @74
    wph
    @23
    @78
    anass
    @99
    @91
    wa
    #
    @73
    @72
    @3
    cin
    #
    c0
    @73
    @101
    wceq
    @100
    @3
    @72
    incom
    a1i
    @100
    vi
    vm
    cE
    cF
    @70
    @2
    cN
    cZ
    iundjiun.z
    @89
    wph
    @23
    @78
    @91
    simplrr
    wph
    @23
    @78
    @91
    simplrl
    @99
    @91
    simpr
    iundjiunlem
    eqtrd
    sylanb
    syl2anc
    pm2.61dan
    ex
    @71
    @74
    df-or
    sylibr
    ralrimiva
    ex
    ralrimi
    @10
    vm
    cZ
    @0
    cF
    cfv
    #
    wdisj
    @0
    @70
    wceq
    #
    @102
    @72
    cin
    #
    c0
    wceq
    #
    wo
    #
    vk
    cZ
    wral
    #
    vm
    cZ
    wral
    @77
    vn
    vm
    cZ
    @3
    @102
    vm
    @3
    nfcv
    vn
    @0
    cF
    vn
    cF
    @83
    iundjiun.f
    vn
    cZ
    @31
    nfmpt1
    nfcxfr
    #
    vn
    @0
    nfcv
    nffv
    #
    @2
    @0
    cF
    fveq2
    cbvdisj
    cZ
    @102
    @72
    vm
    vk
    @0
    @70
    cF
    fveq2
    disjor
    @107
    @76
    vm
    vn
    cZ
    @106
    vn
    vk
    cZ
    vn
    cZ
    nfcv
    @103
    @105
    vn
    @103
    vn
    nfv
    vn
    @104
    c0
    vn
    @102
    @72
    @109
    vn
    @70
    cF
    @108
    vn
    @70
    nfcv
    nffv
    nfin
    vn
    c0
    nfcv
    nfeq
    nfor
    nfral
    @76
    vm
    nfv
    @0
    @2
    wceq
    #
    @106
    @75
    vk
    cZ
    @110
    @103
    @71
    @105
    @74
    vm
    vn
    vk
    equequ1
    @110
    @104
    @73
    c0
    @110
    @102
    @3
    @72
    @0
    @2
    cF
    fveq2
    ineq1d
    eqeq1d
    orbi12d
    ralbidv
    cbvral
    3bitri
    sylibr
    jca31
end
