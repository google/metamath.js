include "caddc.mm"
include "co.mm"
include "climc.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "wne.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "limccl.mm"
include "sseldi.mm"
include "addcld.mm"
include "c2.mm"
include "cdiv.mm"
include "fmptd.mm"
include "limcmptdm.mm"
include "cdm.mm"
include "wf.mm"
include "wss.mm"
include "w3a.mm"
include "limcrcl.mm"
include "syl.mm"
include "simp3d.mm"
include "ellimc3.mm"
include "mpbid.mm"
include "simprd.mm"
include "rphalfcl.mm"
include "wceq.mm"
include "breq2.mm"
include "imbi2d.mm"
include "rexralbidv.mm"
include "rspccva.mm"
include "syl2an.mm"
include "reeanv.mm"
include "sylanbrc.mm"
include "cle.mm"
include "cif.mm"
include "ifcl.mm"
include "3ad2ant2.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "nf3an.mm"
include "cr.mm"
include "simp11l.mm"
include "simp2.mm"
include "jca.mm"
include "rpre.mm"
include "adantl.mm"
include "3ad2ant1.mm"
include "simp13l.mm"
include "simp3l.mm"
include "sselda.mm"
include "syl2anc.mm"
include "subcld.mm"
include "abscld.mm"
include "rpred.mm"
include "simpl.mm"
include "simp3r.mm"
include "simpr.mm"
include "min1.mm"
include "ltletrd.mm"
include "rsp.mm"
include "syl3c.mm"
include "jca31.mm"
include "simp13r.mm"
include "min2.mm"
include "ffvelrnda.mm"
include "ad3antrrr.mm"
include "simp-4l.mm"
include "readdcld.mm"
include "simpllr.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfov.mm"
include "nfeq.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "fvmpt2.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "chvar.mm"
include "oveq1d.mm"
include "addsub4d.mm"
include "fveq2d.mm"
include "abstrid.mm"
include "eqbrtrd.mm"
include "simplr.mm"
include "lt2halvesd.mm"
include "lelttrd.mm"
include "3exp.mm"
include "ralrimi.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "rexlimdvv.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "mpbir2and.mm"

theorem addlimc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume addlimc.f: |- F = ( x e. A |-> B )
  assume addlimc.g: |- G = ( x e. A |-> C )
  assume addlimc.h: |- H = ( x e. A |-> ( B + C ) )
  assume addlimc.b: |- ( ( ph /\ x e. A ) -> B e. CC )
  assume addlimc.c: |- ( ( ph /\ x e. A ) -> C e. CC )
  assume addlimc.e: |- ( ph -> E e. ( F limCC D ) )
  assume addlimc.i: |- ( ph -> I e. ( G limCC D ) )

  disjoint A x
  disjoint ph x
  disjoint A a
  disjoint A b
  disjoint A v
  disjoint A w
  disjoint A y
  disjoint a b
  disjoint a v
  disjoint a w
  disjoint a y
  disjoint b v
  disjoint b w
  disjoint b y
  disjoint v w
  disjoint v y
  disjoint w y
  disjoint v x
  disjoint A z
  disjoint a z
  disjoint b z
  disjoint v z
  disjoint y z
  disjoint D a
  disjoint D b
  disjoint D v
  disjoint D w
  disjoint D y
  disjoint D z
  disjoint E a
  disjoint E b
  disjoint E v
  disjoint E w
  disjoint E y
  disjoint E z
  disjoint F a
  disjoint F b
  disjoint F v
  disjoint F z
  disjoint G a
  disjoint G b
  disjoint G v
  disjoint G z
  disjoint H a
  disjoint H b
  disjoint H v
  disjoint H w
  disjoint H y
  disjoint I a
  disjoint I b
  disjoint I v
  disjoint I w
  disjoint I y
  disjoint I z
  disjoint a ph
  disjoint b ph
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( E + I ) e. ( H limCC D ) )

  proof
    wph
    cE
    cI
    caddc
    co
    #
    cH
    cD
    climc
    co
    wcel
    @0
    cc
    wcel
    #
    vv
    cv
    #
    cD
    wne
    #
    @2
    cD
    cmin
    co
    #
    cabs
    cfv
    #
    vw
    cv
    #
    clt
    wbr
    #
    wa
    #
    @2
    cH
    cfv
    #
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vv
    cA
    wral
    #
    vw
    crp
    wrex
    #
    vy
    crp
    wral
    wph
    cE
    cI
    wph
    cF
    cD
    climc
    co
    #
    cc
    cE
    cD
    cF
    limccl
    addlimc.e
    sseldi
    #
    wph
    cG
    cD
    climc
    co
    #
    cc
    cI
    cD
    cG
    limccl
    addlimc.i
    sseldi
    #
    addcld
    #
    wph
    @16
    vy
    crp
    wph
    @12
    crp
    wcel
    #
    wa
    #
    @3
    @5
    va
    cv
    #
    clt
    wbr
    #
    wa
    #
    @2
    cF
    cfv
    #
    cE
    cmin
    co
    #
    cabs
    cfv
    #
    @12
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    wi
    #
    vv
    cA
    wral
    #
    @3
    @5
    vb
    cv
    #
    clt
    wbr
    #
    wa
    #
    @2
    cG
    cfv
    #
    cI
    cmin
    co
    #
    cabs
    cfv
    #
    @30
    clt
    wbr
    #
    wi
    #
    vv
    cA
    wral
    #
    wa
    #
    vb
    crp
    wrex
    va
    crp
    wrex
    #
    @16
    @23
    @33
    va
    crp
    wrex
    #
    @42
    vb
    crp
    wrex
    #
    @44
    wph
    @26
    @29
    vz
    cv
    #
    clt
    wbr
    #
    wi
    #
    vv
    cA
    wral
    va
    crp
    wrex
    #
    vz
    crp
    wral
    #
    @30
    crp
    wcel
    #
    @45
    @22
    wph
    cE
    cc
    wcel
    #
    @51
    wph
    cE
    @17
    wcel
    #
    @53
    @51
    wa
    addlimc.e
    wph
    vz
    va
    vv
    cA
    cD
    cE
    cF
    wph
    vx
    cA
    cB
    cc
    cF
    addlimc.b
    addlimc.f
    fmptd
    #
    wph
    vx
    cA
    cB
    cE
    cD
    cF
    addlimc.f
    addlimc.b
    addlimc.e
    limcmptdm
    #
    wph
    cF
    cdm
    #
    cc
    cF
    wf
    #
    @57
    cc
    wss
    #
    cD
    cc
    wcel
    #
    wph
    @54
    @58
    @59
    @60
    w3a
    addlimc.e
    cD
    cE
    cF
    limcrcl
    syl
    simp3d
    #
    ellimc3
    mpbid
    simprd
    @12
    rphalfcl
    #
    @50
    @45
    vz
    @30
    crp
    @47
    @30
    wceq
    #
    @49
    @32
    va
    vv
    crp
    cA
    @63
    @48
    @31
    @26
    @47
    @30
    @29
    clt
    breq2
    imbi2d
    rexralbidv
    rspccva
    syl2an
    wph
    @36
    @39
    @47
    clt
    wbr
    #
    wi
    #
    vv
    cA
    wral
    vb
    crp
    wrex
    #
    vz
    crp
    wral
    #
    @52
    @46
    @22
    wph
    cI
    cc
    wcel
    #
    @67
    wph
    cI
    @19
    wcel
    @68
    @67
    wa
    addlimc.i
    wph
    vz
    vb
    vv
    cA
    cD
    cI
    cG
    wph
    vx
    cA
    cC
    cc
    cG
    addlimc.c
    addlimc.g
    fmptd
    #
    @56
    @61
    ellimc3
    mpbid
    simprd
    @62
    @66
    @46
    vz
    @30
    crp
    @63
    @65
    @41
    vb
    vv
    crp
    cA
    @63
    @64
    @40
    @36
    @47
    @30
    @39
    clt
    breq2
    imbi2d
    rexralbidv
    rspccva
    syl2an
    @33
    @42
    va
    vb
    crp
    crp
    reeanv
    sylanbrc
    @23
    @43
    @16
    va
    vb
    crp
    crp
    @23
    @24
    crp
    wcel
    #
    @34
    crp
    wcel
    #
    wa
    #
    @43
    @16
    @23
    @72
    @43
    w3a
    #
    @24
    @34
    cle
    wbr
    #
    @24
    @34
    cif
    #
    crp
    wcel
    #
    @3
    @5
    @75
    clt
    wbr
    #
    wa
    #
    @13
    wi
    #
    vv
    cA
    wral
    #
    @16
    @72
    @23
    @76
    @43
    @74
    @24
    @34
    crp
    ifcl
    3ad2ant2
    #
    @73
    @79
    vv
    cA
    @23
    @72
    @43
    vv
    @23
    vv
    nfv
    @72
    vv
    nfv
    @33
    @42
    vv
    @32
    vv
    cA
    nfra1
    @41
    vv
    cA
    nfra1
    nfan
    nf3an
    @73
    @2
    cA
    wcel
    #
    @78
    @13
    @73
    @82
    @78
    w3a
    #
    wph
    @82
    wa
    #
    @12
    cr
    wcel
    #
    wa
    #
    @31
    wa
    #
    @40
    @13
    @83
    @84
    @85
    @31
    @83
    wph
    @82
    wph
    @22
    @72
    @43
    @82
    @78
    simp11l
    #
    @73
    @82
    @78
    simp2
    #
    jca
    @73
    @82
    @85
    @78
    @23
    @72
    @85
    @43
    @22
    @85
    wph
    @12
    rpre
    adantl
    3ad2ant1
    3ad2ant1
    @83
    @33
    @82
    @26
    @31
    @33
    @42
    @23
    @72
    @82
    @78
    simp13l
    @89
    @83
    @3
    @25
    @73
    @82
    @3
    @77
    simp3l
    #
    @83
    @5
    @75
    @24
    @83
    @4
    @83
    @2
    cD
    @83
    wph
    @82
    @2
    cc
    wcel
    @88
    @89
    wph
    cA
    cc
    @2
    @56
    sselda
    syl2anc
    @83
    wph
    @60
    @88
    @61
    syl
    subcld
    abscld
    #
    @73
    @82
    @75
    cr
    wcel
    @78
    @73
    @75
    @81
    rpred
    3ad2ant1
    #
    @73
    @82
    @24
    cr
    wcel
    #
    @78
    @72
    @23
    @93
    @43
    @72
    @24
    @70
    @71
    simpl
    rpred
    #
    3ad2ant2
    3ad2ant1
    @73
    @82
    @3
    @77
    simp3r
    #
    @73
    @82
    @75
    @24
    cle
    wbr
    #
    @78
    @72
    @23
    @96
    @43
    @72
    @93
    @34
    cr
    wcel
    #
    @96
    @94
    @72
    @34
    @70
    @71
    simpr
    rpred
    #
    @24
    @34
    min1
    syl2anc
    3ad2ant2
    3ad2ant1
    ltletrd
    jca
    @32
    vv
    cA
    rsp
    syl3c
    jca31
    @83
    @42
    @82
    @36
    @40
    @33
    @42
    @23
    @72
    @82
    @78
    simp13r
    @89
    @83
    @3
    @35
    @90
    @83
    @5
    @75
    @34
    @91
    @92
    @73
    @82
    @97
    @78
    @72
    @23
    @97
    @43
    @98
    3ad2ant2
    3ad2ant1
    @95
    @73
    @82
    @75
    @34
    cle
    wbr
    #
    @78
    @72
    @23
    @99
    @43
    @72
    @93
    @97
    @99
    @94
    @98
    @24
    @34
    min2
    syl2anc
    3ad2ant2
    3ad2ant1
    ltletrd
    jca
    @41
    vv
    cA
    rsp
    syl3c
    @87
    @40
    wa
    #
    @11
    @29
    @39
    caddc
    co
    #
    @12
    @100
    @10
    @100
    @9
    @0
    @84
    @9
    cc
    wcel
    @85
    @31
    @40
    wph
    cA
    cc
    @2
    cH
    wph
    vx
    cA
    cB
    cC
    caddc
    co
    #
    cc
    cH
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    cB
    cC
    addlimc.b
    addlimc.c
    addcld
    #
    addlimc.h
    fmptd
    #
    ffvelrnda
    ad3antrrr
    @100
    wph
    @1
    wph
    @82
    @85
    @31
    @40
    simp-4l
    #
    @21
    syl
    subcld
    abscld
    @100
    @29
    @39
    @100
    @28
    @100
    @27
    cE
    @84
    @27
    cc
    wcel
    @85
    @31
    @40
    wph
    cA
    cc
    @2
    cF
    @55
    ffvelrnda
    ad3antrrr
    #
    @100
    wph
    @53
    @108
    @18
    syl
    #
    subcld
    #
    abscld
    #
    @100
    @38
    @100
    @37
    cI
    @84
    @37
    cc
    wcel
    @85
    @31
    @40
    wph
    cA
    cc
    @2
    cG
    @69
    ffvelrnda
    ad3antrrr
    #
    @100
    wph
    @68
    @108
    @20
    syl
    #
    subcld
    #
    abscld
    #
    readdcld
    @84
    @85
    @31
    @40
    simpllr
    #
    @100
    @11
    @28
    @38
    caddc
    co
    #
    cabs
    cfv
    @101
    cle
    @100
    @10
    @118
    cabs
    @100
    @10
    @27
    @37
    caddc
    co
    #
    @0
    cmin
    co
    @118
    @100
    @9
    @119
    @0
    cmin
    @84
    @9
    @119
    wceq
    #
    @85
    @31
    @40
    @105
    @103
    cH
    cfv
    #
    @103
    cF
    cfv
    #
    @103
    cG
    cfv
    #
    caddc
    co
    #
    wceq
    #
    wi
    @84
    @120
    wi
    vx
    vv
    @84
    @120
    vx
    @84
    vx
    nfv
    vx
    @9
    @119
    vx
    @2
    cH
    vx
    cH
    vx
    cA
    @102
    cmpt
    addlimc.h
    vx
    cA
    @102
    nfmpt1
    nfcxfr
    vx
    @2
    nfcv
    #
    nffv
    vx
    @27
    @37
    caddc
    vx
    @2
    cF
    vx
    cF
    vx
    cA
    cB
    cmpt
    addlimc.f
    vx
    cA
    cB
    nfmpt1
    nfcxfr
    @126
    nffv
    vx
    caddc
    nfcv
    vx
    @2
    cG
    vx
    cG
    vx
    cA
    cC
    cmpt
    addlimc.g
    vx
    cA
    cC
    nfmpt1
    nfcxfr
    @126
    nffv
    nfov
    nfeq
    nfim
    @103
    @2
    wceq
    #
    @105
    @84
    @125
    @120
    @127
    @104
    @82
    wph
    @103
    @2
    cA
    eleq1
    anbi2d
    @127
    @121
    @9
    @124
    @119
    @103
    @2
    cH
    fveq2
    @127
    @122
    @27
    @123
    @37
    caddc
    @103
    @2
    cF
    fveq2
    @103
    @2
    cG
    fveq2
    oveq12d
    eqeq12d
    imbi12d
    @105
    @121
    @102
    @124
    @105
    @104
    @102
    cc
    wcel
    @121
    @102
    wceq
    wph
    @104
    simpr
    #
    @106
    vx
    cA
    @102
    cc
    cH
    addlimc.h
    fvmpt2
    syl2anc
    @105
    cB
    @122
    cC
    @123
    caddc
    @105
    @122
    cB
    @105
    @104
    cB
    cc
    wcel
    @122
    cB
    wceq
    @128
    addlimc.b
    vx
    cA
    cB
    cc
    cF
    addlimc.f
    fvmpt2
    syl2anc
    eqcomd
    @105
    @123
    cC
    @105
    @104
    cC
    cc
    wcel
    @123
    cC
    wceq
    @128
    addlimc.c
    vx
    cA
    cC
    cc
    cG
    addlimc.g
    fvmpt2
    syl2anc
    eqcomd
    oveq12d
    eqtrd
    chvar
    ad3antrrr
    oveq1d
    @100
    @27
    @37
    cE
    cI
    @109
    @113
    @110
    @114
    addsub4d
    eqtrd
    fveq2d
    @100
    @28
    @38
    @111
    @115
    abstrid
    eqbrtrd
    @100
    @29
    @39
    @12
    @112
    @116
    @117
    @86
    @31
    @40
    simplr
    @87
    @40
    simpr
    lt2halvesd
    lelttrd
    syl2anc
    3exp
    ralrimi
    @15
    @80
    vw
    @75
    crp
    @6
    @75
    wceq
    #
    @14
    @79
    vv
    cA
    @129
    @8
    @78
    @13
    @129
    @7
    @77
    @3
    @6
    @75
    @5
    clt
    breq2
    anbi2d
    imbi1d
    ralbidv
    rspcev
    syl2anc
    3exp
    rexlimdvv
    mpd
    ralrimiva
    wph
    vy
    vw
    vv
    cA
    cD
    @0
    cH
    @107
    @56
    @61
    ellimc3
    mpbir2and
end
