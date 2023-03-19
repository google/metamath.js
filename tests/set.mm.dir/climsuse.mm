include "cli.mm"
include "wbr.mm"
include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "cz.mm"
include "wrex.mm"
include "crp.mm"
include "climcl.mm"
include "syl.mm"
include "nfv.mm"
include "cle.mm"
include "cif.mm"
include "simpllr.mm"
include "wn.mm"
include "ad4antr.mm"
include "ifclda.mm"
include "nfra1.mm"
include "nfan.mm"
include "simp-4l.mm"
include "jca.mm"
include "simpr.mm"
include "wss.mm"
include "wb.mm"
include "anim1i.mm"
include "adantr.mm"
include "eluz.mm"
include "mpbird.mm"
include "simpll.mm"
include "uzid.mm"
include "3syl.mm"
include "uzss.mm"
include "syl6sseqr.mm"
include "sseld.mm"
include "sylc.mm"
include "wceq.mm"
include "wi.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfeq.mm"
include "nfim.mm"
include "weq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "adantl.mm"
include "c1.mm"
include "caddc.mm"
include "nfov.mm"
include "nfel.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eleq12d.mm"
include "climsuselem1.mm"
include "sseldd.mm"
include "syl6eleqr.mm"
include "ex.mm"
include "imdistani.mm"
include "nfci.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "vtoclgf.mm"
include "eqeltrd.mm"
include "syl2anc.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "cbvralv.mm"
include "ad2antlr.mm"
include "w3a.mm"
include "cr.mm"
include "zre.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "eluzelz.mm"
include "simp1.mm"
include "zred.mm"
include "simpl2.mm"
include "max1.mm"
include "eluzle.mm"
include "3ad2ant3.mm"
include "letrd.mm"
include "eluzelre.mm"
include "max2.mm"
include "simp2.mm"
include "syl3anc.mm"
include "rspccva.mm"
include "simprd.mm"
include "eqbrtrd.mm"
include "ralrimi.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "eqidd.mm"
include "clim.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "r19.29a.mm"
include "mpbir2and.mm"

theorem climsuse
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let vx: setvar x
  let vl: setvar l
  assume climsuse.1: |- F/ k ph
  assume climsuse.3: |- F/_ k F
  assume climsuse.2: |- F/_ k G
  assume climsuse.4: |- F/_ k I
  assume climsuse.5: |- Z = ( ZZ>= ` M )
  assume climsuse.6: |- ( ph -> M e. ZZ )
  assume climsuse.7: |- ( ph -> F e. X )
  assume climsuse.8: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume climsuse.9: |- ( ph -> F ~~> A )
  assume climsuse.10: |- ( ph -> ( I ` M ) e. Z )
  assume climsuse.11: |- ( ( ph /\ k e. Z ) -> ( I ` ( k + 1 ) ) e. ( ZZ>= ` ( ( I ` k ) + 1 ) ) )
  assume climsuse.12: |- ( ph -> G e. Y )
  assume climsuse.13: |- ( ( ph /\ k e. Z ) -> ( G ` k ) = ( F ` ( I ` k ) ) )

  disjoint Z k
  disjoint h i
  disjoint h j
  disjoint h x
  disjoint i j
  disjoint i x
  disjoint j x
  disjoint i k
  disjoint i l
  disjoint i ph
  disjoint j l
  disjoint j ph
  disjoint l x
  disjoint l ph
  disjoint ph x
  disjoint A h
  disjoint A i
  disjoint A j
  disjoint A l
  disjoint A x
  disjoint F h
  disjoint F i
  disjoint F j
  disjoint F x
  disjoint G i
  disjoint G j
  disjoint G l
  disjoint G x
  disjoint I h
  disjoint I i
  disjoint M i
  disjoint M l
  disjoint Z i
  assert |- ( ph -> G ~~> A )

  proof
    wph
    cG
    cA
    cli
    wbr
    cA
    cc
    wcel
    #
    vi
    cv
    #
    cG
    cfv
    #
    cc
    wcel
    #
    @2
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wa
    #
    vi
    vl
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vl
    cz
    wrex
    #
    vx
    crp
    wral
    wph
    cF
    cA
    cli
    wbr
    #
    @0
    climsuse.9
    cA
    cF
    climcl
    syl
    wph
    @12
    vx
    crp
    wph
    vx
    nfv
    wph
    @6
    crp
    wcel
    #
    @12
    wph
    @14
    wa
    #
    @1
    cF
    cfv
    #
    cc
    wcel
    #
    @16
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    clt
    wbr
    #
    wa
    #
    vi
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    @12
    vj
    cz
    @15
    @22
    cz
    wcel
    #
    wa
    #
    @24
    wa
    #
    cM
    @22
    cle
    wbr
    #
    @22
    cM
    cif
    #
    cz
    wcel
    @8
    vi
    @29
    cuz
    cfv
    #
    wral
    #
    @12
    @27
    @28
    @22
    cM
    cz
    @15
    @25
    @24
    @28
    simpllr
    wph
    cM
    cz
    wcel
    #
    @14
    @25
    @24
    @28
    wn
    #
    climsuse.6
    ad4antr
    ifclda
    @27
    @8
    vi
    @30
    @26
    @24
    vi
    @26
    vi
    nfv
    @21
    vi
    @23
    nfra1
    nfan
    @27
    @1
    @30
    wcel
    #
    @8
    @27
    @34
    wa
    #
    @3
    @7
    @35
    wph
    @1
    cZ
    wcel
    #
    @3
    wph
    @14
    @25
    @24
    @34
    simp-4l
    #
    @35
    wph
    @25
    wa
    #
    @34
    @36
    @35
    wph
    @25
    @37
    @15
    @25
    @24
    @34
    simpllr
    #
    jca
    @27
    @34
    simpr
    #
    @38
    @30
    cZ
    @1
    @38
    @30
    cM
    cuz
    cfv
    #
    cZ
    @38
    @29
    @41
    wcel
    @30
    @41
    wss
    @38
    @28
    @22
    cM
    @41
    @38
    @28
    wa
    #
    @22
    @41
    wcel
    #
    @28
    @38
    @28
    simpr
    @42
    @32
    @25
    wa
    #
    @43
    @28
    wb
    @38
    @44
    @28
    wph
    @32
    @25
    climsuse.6
    anim1i
    adantr
    cM
    @22
    eluz
    syl
    mpbird
    @38
    @33
    wa
    wph
    @32
    cM
    @41
    wcel
    wph
    @25
    @33
    simpll
    climsuse.6
    cM
    uzid
    3syl
    ifclda
    cM
    @29
    uzss
    syl
    climsuse.5
    syl6sseqr
    sseld
    sylc
    #
    wph
    @36
    wa
    #
    @2
    @1
    cI
    cfv
    #
    cF
    cfv
    #
    cc
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @49
    cG
    cfv
    #
    @49
    cI
    cfv
    #
    cF
    cfv
    #
    wceq
    #
    wi
    @46
    @2
    @48
    wceq
    #
    wi
    vk
    vi
    @46
    @56
    vk
    wph
    @36
    vk
    climsuse.1
    @36
    vk
    nfv
    #
    nfan
    #
    vk
    @2
    @48
    vk
    @1
    cG
    climsuse.2
    vk
    @1
    nfcv
    #
    nffv
    vk
    @47
    cF
    climsuse.3
    vk
    @1
    cI
    climsuse.4
    @59
    nffv
    #
    nffv
    #
    nfeq
    nfim
    vk
    vi
    weq
    #
    @51
    @46
    @55
    @56
    @62
    @50
    @36
    wph
    @49
    @1
    cZ
    eleq1
    anbi2d
    #
    @62
    @52
    @2
    @54
    @48
    @49
    @1
    cG
    fveq2
    @62
    @53
    @47
    cF
    @49
    @1
    cI
    fveq2
    #
    fveq2d
    eqeq12d
    imbi12d
    climsuse.13
    chvar
    #
    @46
    @47
    cZ
    wcel
    #
    wph
    @66
    wa
    #
    @48
    cc
    wcel
    #
    @46
    @47
    @41
    cZ
    @46
    @1
    cuz
    cfv
    #
    @41
    @47
    @46
    @1
    @41
    wcel
    #
    @69
    @41
    wss
    @36
    @70
    wph
    @36
    @70
    cZ
    @41
    @1
    climsuse.5
    eleq2i
    biimpi
    adantl
    cM
    @1
    uzss
    syl
    wph
    vi
    cI
    @1
    cM
    cZ
    climsuse.5
    climsuse.6
    climsuse.10
    @51
    @49
    c1
    caddc
    co
    #
    cI
    cfv
    #
    @53
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    wi
    @46
    @1
    c1
    caddc
    co
    #
    cI
    cfv
    #
    @47
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    wi
    vk
    vi
    @46
    @80
    vk
    @58
    vk
    @77
    @79
    vk
    @76
    cI
    climsuse.4
    vk
    @76
    nfcv
    nffv
    vk
    @78
    cuz
    vk
    cuz
    nfcv
    vk
    @47
    c1
    caddc
    @60
    vk
    caddc
    nfcv
    vk
    c1
    nfcv
    nfov
    nffv
    nfel
    nfim
    @62
    @51
    @46
    @75
    @80
    @63
    @62
    @72
    @77
    @74
    @79
    @62
    @71
    @76
    cI
    @49
    @1
    c1
    caddc
    oveq1
    fveq2d
    @62
    @73
    @78
    cuz
    @62
    @53
    @47
    c1
    caddc
    @64
    oveq1d
    fveq2d
    eleq12d
    imbi12d
    climsuse.11
    chvar
    climsuselem1
    #
    sseldd
    #
    climsuse.5
    syl6eleqr
    #
    wph
    @36
    @66
    wph
    @36
    @66
    @83
    ex
    imdistani
    @51
    @49
    cF
    cfv
    #
    cc
    wcel
    #
    wi
    @67
    @68
    wi
    vk
    @47
    cZ
    @60
    @67
    @68
    vk
    wph
    @66
    vk
    climsuse.1
    vk
    @47
    cZ
    @60
    vk
    vi
    cZ
    @57
    nfci
    nfel
    nfan
    vk
    @48
    cc
    @61
    nfel1
    nfim
    @49
    @47
    wceq
    #
    @51
    @67
    @85
    @68
    @86
    @50
    @66
    wph
    @49
    @47
    cZ
    eleq1
    anbi2d
    @86
    @84
    @48
    cc
    @49
    @47
    cF
    fveq2
    eleq1d
    imbi12d
    climsuse.8
    vtoclgf
    sylc
    eqeltrd
    syl2anc
    @35
    @5
    @48
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    clt
    @35
    @4
    @87
    cabs
    @35
    @2
    @48
    cA
    cmin
    @35
    wph
    @36
    @56
    @37
    @45
    @65
    syl2anc
    oveq1d
    fveq2d
    @35
    vh
    cv
    #
    cF
    cfv
    #
    cc
    wcel
    #
    @90
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    clt
    wbr
    #
    wa
    #
    vh
    @23
    wral
    #
    @47
    @23
    wcel
    #
    @88
    @6
    clt
    wbr
    #
    @24
    @96
    @26
    @34
    @24
    @96
    @21
    @95
    vi
    vh
    @23
    vi
    vh
    weq
    #
    @17
    @91
    @20
    @94
    @99
    @16
    @90
    cc
    @1
    @89
    cF
    fveq2
    #
    eleq1d
    @99
    @19
    @93
    @6
    clt
    @99
    @18
    @92
    cabs
    @99
    @16
    @90
    cA
    cmin
    @100
    oveq1d
    fveq2d
    breq1d
    anbi12d
    cbvralv
    biimpi
    ad2antlr
    @35
    wph
    @25
    @34
    @97
    @37
    @39
    @40
    wph
    @25
    @34
    w3a
    #
    @97
    @22
    @47
    cle
    wbr
    #
    @101
    @22
    @1
    @47
    @25
    wph
    @22
    cr
    wcel
    #
    @34
    @22
    zre
    3ad2ant2
    #
    @101
    @34
    @1
    cz
    wcel
    #
    @1
    cr
    wcel
    wph
    @25
    @34
    simp3
    @29
    @1
    eluzelz
    #
    @1
    zre
    3syl
    #
    @101
    @46
    @47
    @41
    wcel
    @47
    cr
    wcel
    @101
    wph
    @36
    wph
    @25
    @34
    simp1
    #
    @101
    @1
    @41
    cZ
    @101
    @70
    cM
    @1
    cle
    wbr
    #
    @101
    cM
    @29
    @1
    @101
    wph
    cM
    cr
    wcel
    #
    @108
    wph
    cM
    climsuse.6
    zred
    syl
    #
    @101
    @28
    @22
    cM
    cr
    @101
    @28
    wa
    @22
    wph
    @25
    @34
    @28
    simpl2
    zred
    @101
    @110
    @33
    @111
    adantr
    ifclda
    #
    @107
    @101
    @110
    @103
    cM
    @29
    cle
    wbr
    @111
    @104
    cM
    @22
    max1
    syl2anc
    @34
    wph
    @29
    @1
    cle
    wbr
    @25
    @29
    @1
    eluzle
    3ad2ant3
    #
    letrd
    @101
    @32
    @105
    @70
    @109
    wb
    @101
    wph
    @32
    @108
    climsuse.6
    syl
    @34
    wph
    @105
    @25
    @106
    3ad2ant3
    cM
    @1
    eluz
    syl2anc
    mpbird
    climsuse.5
    syl6eleqr
    jca
    #
    @82
    cM
    @47
    eluzelre
    3syl
    @101
    @22
    @29
    @1
    @104
    @112
    @107
    @101
    @110
    @103
    @22
    @29
    cle
    wbr
    @111
    @104
    cM
    @22
    max2
    syl2anc
    @113
    letrd
    @101
    @46
    @47
    @69
    wcel
    #
    @1
    @47
    cle
    wbr
    @114
    @81
    @1
    @47
    eluzle
    3syl
    letrd
    @101
    @25
    @47
    cz
    wcel
    #
    @97
    @102
    wb
    wph
    @25
    @34
    simp2
    @101
    @46
    @115
    @116
    @114
    @81
    @1
    @47
    eluzelz
    3syl
    @22
    @47
    eluz
    syl2anc
    mpbird
    syl3anc
    @96
    @97
    wa
    @68
    @98
    @95
    @68
    @98
    wa
    vh
    @47
    @23
    @89
    @47
    wceq
    #
    @91
    @68
    @94
    @98
    @117
    @90
    @48
    cc
    @89
    @47
    cF
    fveq2
    #
    eleq1d
    @117
    @93
    @88
    @6
    clt
    @117
    @92
    @87
    cabs
    @117
    @90
    @48
    cA
    cmin
    @118
    oveq1d
    fveq2d
    breq1d
    anbi12d
    rspccva
    simprd
    syl2anc
    eqbrtrd
    jca
    ex
    ralrimi
    @11
    @31
    vl
    @29
    cz
    @9
    @29
    wceq
    @8
    vi
    @10
    @30
    @9
    @29
    cuz
    fveq2
    raleqdv
    rspcev
    syl2anc
    wph
    @24
    vj
    cz
    wrex
    #
    vx
    crp
    wph
    @0
    @119
    vx
    crp
    wral
    #
    wph
    @13
    @0
    @120
    wa
    climsuse.9
    wph
    vx
    cA
    @16
    vj
    vi
    cF
    cX
    climsuse.7
    wph
    @105
    wa
    #
    @16
    eqidd
    clim
    mpbid
    simprd
    r19.21bi
    r19.29a
    ex
    ralrimi
    wph
    vx
    cA
    @2
    vl
    vi
    cG
    cY
    climsuse.12
    @121
    @2
    eqidd
    clim
    mpbir2and
end
