include "cc0.mm"
include "climc.mm"
include "co.mm"
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
include "0cnd.mm"
include "c2.mm"
include "cdiv.mm"
include "csn.mm"
include "eldifad.mm"
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
include "simpld.mm"
include "absrpcld.mm"
include "rphalfcld.mm"
include "wceq.mm"
include "breq2.mm"
include "imbi2d.mm"
include "rexralbidv.mm"
include "rspccva.mm"
include "syl2anc.mm"
include "simpl1l.mm"
include "simpl3.mm"
include "simpr.mm"
include "simpl2.mm"
include "mp2d.mm"
include "caddc.mm"
include "rpcnd.mm"
include "2halvesd.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "2cnd.mm"
include "2ne0.mm"
include "a1i.mm"
include "absdivd.mm"
include "cr.mm"
include "2re.mm"
include "cle.mm"
include "0le2.mm"
include "absidd.mm"
include "oveq2d.mm"
include "eqtr2d.mm"
include "pncand.mm"
include "3eqtr3rd.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "abscld.mm"
include "3adant3.mm"
include "ffvelrnda.mm"
include "subcld.mm"
include "readdcld.mm"
include "rehalfcld.mm"
include "pncan3d.mm"
include "fveq2d.mm"
include "abstrid.mm"
include "eqbrtrd.mm"
include "abssubd.mm"
include "simp3.mm"
include "ltadd2dd.mm"
include "lelttrd.mm"
include "ltsubaddd.mm"
include "mpbird.mm"
include "syl3anc.mm"
include "3exp1.mm"
include "ralimdv2.mm"
include "reximdva.mm"
include "mpd.mm"
include "cmul.mm"
include "rpmulcld.mm"
include "ex.mm"
include "imdistani.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "imbi12d.mm"
include "r19.21bi.mm"
include "vtoclg.mm"
include "sylc.mm"
include "cif.mm"
include "simp12.mm"
include "simp2.mm"
include "ifcld.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "simp111.mm"
include "simp112.mm"
include "jca31.mm"
include "simp3l.mm"
include "sseldd.mm"
include "rpred.mm"
include "simp3r.mm"
include "min1.mm"
include "ltletrd.mm"
include "simp113.mm"
include "rspa.mm"
include "mp2and.mm"
include "simp13.mm"
include "min2.mm"
include "jca.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfel1.mm"
include "nfim.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "fvmpt2.mm"
include "eqeltrd.mm"
include "chvar.mm"
include "subid1d.mm"
include "mpd3an23.mm"
include "simp-7l.mm"
include "simp-4r.mm"
include "cdif.mm"
include "eldifsni.mm"
include "divcld.mm"
include "nfov.mm"
include "nfeq.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "eqtrd.mm"
include "simp-6l.mm"
include "simplr.mm"
include "nfne.mm"
include "neeq1d.mm"
include "eqnetrd.mm"
include "adantlr.mm"
include "ad2antrr.mm"
include "absne0d.mm"
include "redivcld.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "remulcld.mm"
include "rerpdivcld.mm"
include "simp-4l.mm"
include "simpllr.mm"
include "ltdiv1dd.mm"
include "c1.mm"
include "recnd.mm"
include "divassd.mm"
include "1red.mm"
include "1rp.mm"
include "div1d.mm"
include "ltdiv23d.mm"
include "adantllr.mm"
include "ltmul2dd.mm"
include "mulid1d.mm"
include "breqtrd.mm"
include "lttrd.mm"
include "syl21anc.mm"
include "3exp.mm"
include "ralrimi.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "rexlimdv3a.mm"
include "ralrimiva.mm"
include "mpbir2and.mm"

theorem 0ellimcdiv
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
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume 0ellimcdiv.f: |- F = ( x e. A |-> B )
  assume 0ellimcdiv.g: |- G = ( x e. A |-> C )
  assume 0ellimcdiv.h: |- H = ( x e. A |-> ( B / C ) )
  assume 0ellimcdiv.b: |- ( ( ph /\ x e. A ) -> B e. CC )
  assume 0ellimcdiv.c: |- ( ( ph /\ x e. A ) -> C e. ( CC \ { 0 } ) )
  assume 0ellimcdiv.0limf: |- ( ph -> 0 e. ( F limCC E ) )
  assume 0ellimcdiv.d: |- ( ph -> D e. ( G limCC E ) )
  assume 0ellimcdiv.dne0: |- ( ph -> D =/= 0 )

  disjoint A x
  disjoint ph x
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint v x
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D y
  disjoint D z
  disjoint E u
  disjoint E v
  disjoint E w
  disjoint E y
  disjoint E z
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint G u
  disjoint G v
  disjoint G y
  disjoint G z
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H y
  disjoint H z
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> 0 e. ( H limCC E ) )

  proof
    wph
    cc0
    cH
    cE
    climc
    co
    wcel
    cc0
    cc
    wcel
    #
    vv
    cv
    #
    cE
    wne
    #
    @1
    cE
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
    @1
    cH
    cfv
    #
    cc0
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
    0cnd
    wph
    @15
    vy
    crp
    wph
    @11
    crp
    wcel
    #
    wa
    #
    @2
    @4
    vz
    cv
    #
    clt
    wbr
    #
    wa
    #
    cD
    cabs
    cfv
    #
    c2
    cdiv
    co
    #
    @1
    cG
    cfv
    #
    cabs
    cfv
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
    vz
    crp
    wrex
    #
    @15
    wph
    @28
    @16
    wph
    @20
    @23
    cD
    cmin
    co
    cabs
    cfv
    #
    @22
    clt
    wbr
    #
    wi
    #
    vv
    cA
    wral
    #
    vz
    crp
    wrex
    #
    @28
    wph
    @20
    @29
    @11
    clt
    wbr
    #
    wi
    #
    vv
    cA
    wral
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    #
    @22
    crp
    wcel
    @33
    wph
    cD
    cc
    wcel
    #
    @37
    wph
    cD
    cG
    cE
    climc
    co
    wcel
    #
    @38
    @37
    wa
    0ellimcdiv.d
    wph
    vy
    vz
    vv
    cA
    cE
    cD
    cG
    wph
    vx
    cA
    cC
    cc
    cG
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    cC
    cc
    cc0
    csn
    #
    0ellimcdiv.c
    eldifad
    #
    0ellimcdiv.g
    fmptd
    #
    wph
    vx
    cA
    cB
    cc0
    cE
    cF
    0ellimcdiv.f
    0ellimcdiv.b
    0ellimcdiv.0limf
    limcmptdm
    #
    wph
    cG
    cdm
    #
    cc
    cG
    wf
    #
    @47
    cc
    wss
    #
    cE
    cc
    wcel
    #
    wph
    @39
    @48
    @49
    @50
    w3a
    0ellimcdiv.d
    cE
    cD
    cG
    limcrcl
    syl
    simp3d
    #
    ellimc3
    mpbid
    #
    simprd
    wph
    @21
    wph
    cD
    wph
    @38
    @37
    @52
    simpld
    #
    0ellimcdiv.dne0
    absrpcld
    #
    rphalfcld
    #
    @36
    @33
    vy
    @22
    crp
    @11
    @22
    wceq
    #
    @35
    @31
    vz
    vv
    crp
    cA
    @56
    @34
    @30
    @20
    @11
    @22
    @29
    clt
    breq2
    imbi2d
    rexralbidv
    rspccva
    syl2anc
    wph
    @32
    @27
    vz
    crp
    wph
    @18
    crp
    wcel
    #
    wa
    #
    @31
    @26
    vv
    cA
    cA
    @58
    @1
    cA
    wcel
    #
    @31
    wi
    #
    @59
    @20
    @25
    @58
    @60
    @59
    w3a
    #
    @20
    wa
    #
    wph
    @59
    @30
    @25
    wph
    @57
    @60
    @59
    @20
    simpl1l
    @58
    @60
    @59
    @20
    simpl3
    #
    @62
    @59
    @20
    @30
    @63
    @61
    @20
    simpr
    @58
    @60
    @59
    @20
    simpl2
    mp2d
    wph
    @59
    @30
    w3a
    #
    @22
    @21
    cD
    c2
    cdiv
    co
    cabs
    cfv
    #
    cmin
    co
    #
    @24
    clt
    wph
    @59
    @22
    @66
    wceq
    @30
    wph
    @21
    @22
    cmin
    co
    #
    @22
    @22
    caddc
    co
    #
    @22
    cmin
    co
    @66
    @22
    wph
    @21
    @68
    @22
    cmin
    wph
    @68
    @21
    wph
    @21
    wph
    @21
    @54
    rpcnd
    2halvesd
    eqcomd
    oveq1d
    wph
    @22
    @65
    @21
    cmin
    wph
    @65
    @21
    c2
    cabs
    cfv
    #
    cdiv
    co
    @22
    wph
    cD
    c2
    @53
    wph
    2cnd
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    absdivd
    wph
    @69
    c2
    @21
    cdiv
    wph
    c2
    c2
    cr
    wcel
    wph
    2re
    a1i
    cc0
    c2
    cle
    wbr
    wph
    0le2
    a1i
    absidd
    oveq2d
    eqtr2d
    #
    oveq2d
    wph
    @22
    @22
    wph
    @22
    @55
    rpcnd
    #
    @71
    pncand
    3eqtr3rd
    3ad2ant1
    @64
    @66
    @67
    @24
    clt
    @64
    @65
    @22
    @21
    cmin
    wph
    @59
    @65
    @22
    wceq
    @30
    wph
    @22
    @65
    @70
    eqcomd
    3ad2ant1
    oveq2d
    @64
    @67
    @24
    clt
    wbr
    @21
    @24
    @22
    caddc
    co
    #
    clt
    wbr
    @64
    @21
    @24
    cD
    @23
    cmin
    co
    #
    cabs
    cfv
    #
    caddc
    co
    #
    @72
    wph
    @59
    @21
    cr
    wcel
    @30
    wph
    @59
    wa
    #
    cD
    wph
    @38
    @59
    @53
    adantr
    #
    abscld
    3adant3
    #
    @64
    @24
    @74
    @64
    @23
    wph
    @59
    @23
    cc
    wcel
    @30
    wph
    cA
    cc
    @1
    cG
    @45
    ffvelrnda
    #
    3adant3
    #
    abscld
    #
    @64
    @73
    @64
    cD
    @23
    wph
    @59
    @38
    @30
    @53
    3ad2ant1
    #
    @80
    subcld
    abscld
    #
    readdcld
    @64
    @24
    @22
    @81
    @64
    @21
    @78
    rehalfcld
    #
    readdcld
    wph
    @59
    @21
    @75
    cle
    wbr
    @30
    @76
    @21
    @23
    @73
    caddc
    co
    #
    cabs
    cfv
    @75
    cle
    @76
    cD
    @85
    cabs
    @76
    @85
    cD
    @76
    @23
    cD
    @79
    @77
    pncan3d
    eqcomd
    fveq2d
    @76
    @23
    @73
    @79
    @76
    cD
    @23
    @77
    @79
    subcld
    abstrid
    eqbrtrd
    3adant3
    @64
    @74
    @22
    @24
    @83
    @84
    @81
    @64
    @74
    @29
    @22
    clt
    @64
    cD
    @23
    @82
    @80
    abssubd
    wph
    @59
    @30
    simp3
    eqbrtrd
    ltadd2dd
    lelttrd
    @64
    @21
    @22
    @24
    @78
    @84
    wph
    @59
    @24
    cr
    wcel
    @30
    @76
    @23
    @79
    abscld
    #
    3adant3
    ltsubaddd
    mpbird
    eqbrtrd
    eqbrtrd
    syl3anc
    3exp1
    ralimdv2
    reximdva
    mpd
    adantr
    @17
    @27
    @15
    vz
    crp
    @17
    @57
    @27
    w3a
    #
    @2
    @4
    vu
    cv
    #
    clt
    wbr
    #
    wa
    #
    @1
    cF
    cfv
    #
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    @11
    @22
    cmul
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
    vu
    crp
    wrex
    #
    @15
    @17
    @57
    @98
    @27
    @17
    @94
    crp
    wcel
    #
    wph
    @99
    wa
    #
    @98
    @17
    @11
    @22
    wph
    @16
    simpr
    @17
    @21
    @17
    cD
    wph
    @38
    @16
    @53
    adantr
    wph
    cD
    cc0
    wne
    @16
    0ellimcdiv.dne0
    adantr
    absrpcld
    rphalfcld
    rpmulcld
    #
    wph
    @16
    @99
    wph
    @16
    @99
    @101
    ex
    imdistani
    wph
    @5
    crp
    wcel
    #
    wa
    #
    @90
    @93
    @5
    clt
    wbr
    #
    wi
    #
    vv
    cA
    wral
    vu
    crp
    wrex
    #
    wi
    @100
    @98
    wi
    vw
    @94
    crp
    @5
    @94
    wceq
    #
    @103
    @100
    @106
    @98
    @107
    @102
    @99
    wph
    @5
    @94
    crp
    eleq1
    anbi2d
    @107
    @105
    @96
    vu
    vv
    crp
    cA
    @107
    @104
    @95
    @90
    @5
    @94
    @93
    clt
    breq2
    imbi2d
    rexralbidv
    imbi12d
    wph
    @106
    vw
    crp
    wph
    @0
    @106
    vw
    crp
    wral
    #
    wph
    cc0
    cF
    cE
    climc
    co
    wcel
    @0
    @108
    wa
    0ellimcdiv.0limf
    wph
    vw
    vu
    vv
    cA
    cE
    cc0
    cF
    wph
    vx
    cA
    cB
    cc
    cF
    0ellimcdiv.b
    0ellimcdiv.f
    fmptd
    @46
    @51
    ellimc3
    mpbid
    simprd
    r19.21bi
    vtoclg
    sylc
    3ad2ant1
    @87
    @97
    @15
    vu
    crp
    @87
    @88
    crp
    wcel
    #
    @97
    w3a
    #
    @18
    @88
    cle
    wbr
    #
    @18
    @88
    cif
    #
    crp
    wcel
    @2
    @4
    @112
    clt
    wbr
    #
    wa
    #
    @12
    wi
    #
    vv
    cA
    wral
    #
    @15
    @110
    @111
    @18
    @88
    crp
    @17
    @57
    @27
    @109
    @97
    simp12
    @87
    @109
    @97
    simp2
    ifcld
    @110
    @115
    vv
    cA
    @87
    @109
    @97
    vv
    @17
    @57
    @27
    vv
    @17
    vv
    nfv
    @57
    vv
    nfv
    @26
    vv
    cA
    nfra1
    nf3an
    @109
    vv
    nfv
    @96
    vv
    cA
    nfra1
    nf3an
    @110
    @59
    @114
    @12
    @110
    @59
    @114
    w3a
    #
    @17
    @57
    wa
    @109
    wa
    #
    @59
    wa
    @2
    wa
    #
    @25
    @91
    cabs
    cfv
    #
    @94
    clt
    wbr
    #
    @12
    @117
    @118
    @59
    @2
    @117
    @17
    @57
    @109
    @17
    @57
    @27
    @109
    @97
    @59
    @114
    simp111
    #
    @17
    @57
    @27
    @109
    @97
    @59
    @114
    simp112
    #
    @87
    @109
    @97
    @59
    @114
    simp12
    #
    jca31
    @110
    @59
    @114
    simp2
    #
    @110
    @59
    @2
    @113
    simp3l
    #
    jca31
    @117
    @2
    @19
    @25
    @126
    @117
    @4
    @112
    @18
    @117
    @3
    @117
    @1
    cE
    @117
    cA
    cc
    @1
    @110
    @59
    cA
    cc
    wss
    #
    @114
    @87
    @109
    @127
    @97
    @17
    @57
    @127
    @27
    wph
    @127
    @16
    @46
    adantr
    3ad2ant1
    3ad2ant1
    3ad2ant1
    @125
    sseldd
    @110
    @59
    @50
    @114
    @87
    @109
    @50
    @97
    @17
    @57
    @50
    @27
    wph
    @50
    @16
    @51
    adantr
    3ad2ant1
    3ad2ant1
    3ad2ant1
    subcld
    abscld
    #
    @117
    @111
    @18
    @88
    cr
    @117
    @18
    @123
    rpred
    #
    @117
    @88
    @124
    rpred
    #
    ifcld
    #
    @129
    @110
    @59
    @2
    @113
    simp3r
    #
    @117
    @18
    cr
    wcel
    #
    @88
    cr
    wcel
    #
    @112
    @18
    cle
    wbr
    @129
    @130
    @18
    @88
    min1
    syl2anc
    ltletrd
    @117
    @27
    @59
    @26
    @17
    @57
    @27
    @109
    @97
    @59
    @114
    simp113
    @125
    @26
    vv
    cA
    rspa
    syl2anc
    mp2and
    @117
    @96
    @90
    @121
    @117
    @97
    @59
    @96
    @87
    @109
    @97
    @59
    @114
    simp13
    @125
    @96
    vv
    cA
    rspa
    syl2anc
    @117
    @2
    @89
    @126
    @117
    @4
    @112
    @88
    @128
    @131
    @130
    @132
    @117
    @133
    @134
    @112
    @88
    cle
    wbr
    @129
    @130
    @18
    @88
    min2
    syl2anc
    ltletrd
    jca
    @117
    @96
    @90
    w3a
    #
    @120
    @93
    @94
    clt
    @135
    wph
    @59
    @120
    @93
    wceq
    @117
    @96
    wph
    @90
    @117
    wph
    @16
    @122
    simpld
    3ad2ant1
    @110
    @59
    @114
    @96
    @90
    simp12
    @76
    @91
    @92
    cabs
    @76
    @92
    @91
    @76
    @91
    @42
    @40
    cF
    cfv
    #
    cc
    wcel
    #
    wi
    @76
    @91
    cc
    wcel
    #
    wi
    vx
    vv
    @76
    @138
    vx
    @76
    vx
    nfv
    #
    vx
    @91
    cc
    vx
    @1
    cF
    vx
    cF
    vx
    cA
    cB
    cmpt
    0ellimcdiv.f
    vx
    cA
    cB
    nfmpt1
    nfcxfr
    vx
    @1
    nfcv
    #
    nffv
    #
    nfel1
    nfim
    @40
    @1
    wceq
    #
    @42
    @76
    @137
    @138
    @142
    @41
    @59
    wph
    @40
    @1
    cA
    eleq1
    anbi2d
    #
    @142
    @136
    @91
    cc
    @40
    @1
    cF
    fveq2
    #
    eleq1d
    imbi12d
    @42
    @136
    cB
    cc
    @42
    @41
    cB
    cc
    wcel
    @136
    cB
    wceq
    wph
    @41
    simpr
    #
    0ellimcdiv.b
    vx
    cA
    cB
    cc
    cF
    0ellimcdiv.f
    fvmpt2
    syl2anc
    #
    0ellimcdiv.b
    eqeltrd
    chvar
    #
    subid1d
    eqcomd
    fveq2d
    syl2anc
    @135
    @90
    @95
    @117
    @96
    @90
    simp3
    @117
    @96
    @90
    simp2
    mpd
    eqbrtrd
    mpd3an23
    @119
    @25
    wa
    #
    @121
    wa
    #
    @10
    @91
    @23
    cdiv
    co
    #
    cabs
    cfv
    #
    @11
    clt
    @149
    wph
    @59
    @10
    @151
    wceq
    wph
    @16
    @57
    @109
    @59
    @2
    @25
    @121
    simp-7l
    @118
    @59
    @2
    @25
    @121
    simp-4r
    #
    @76
    @9
    @150
    cabs
    @76
    @9
    @8
    @150
    @76
    @8
    wph
    cA
    cc
    @1
    cH
    wph
    vx
    cA
    cB
    cC
    cdiv
    co
    #
    cc
    cH
    @42
    cB
    cC
    0ellimcdiv.b
    @44
    @42
    cC
    cc
    @43
    cdif
    #
    wcel
    #
    cC
    cc0
    wne
    0ellimcdiv.c
    cC
    cc
    cc0
    eldifsni
    syl
    #
    divcld
    #
    0ellimcdiv.h
    fmptd
    #
    ffvelrnda
    subid1d
    @42
    @40
    cH
    cfv
    #
    @136
    @40
    cG
    cfv
    #
    cdiv
    co
    #
    wceq
    #
    wi
    @76
    @8
    @150
    wceq
    #
    wi
    vx
    vv
    @76
    @163
    vx
    @139
    vx
    @8
    @150
    vx
    @1
    cH
    vx
    cH
    vx
    cA
    @153
    cmpt
    0ellimcdiv.h
    vx
    cA
    @153
    nfmpt1
    nfcxfr
    @140
    nffv
    vx
    @91
    @23
    cdiv
    @141
    vx
    cdiv
    nfcv
    vx
    @1
    cG
    vx
    cG
    vx
    cA
    cC
    cmpt
    0ellimcdiv.g
    vx
    cA
    cC
    nfmpt1
    nfcxfr
    @140
    nffv
    #
    nfov
    nfeq
    nfim
    @142
    @42
    @76
    @162
    @163
    @143
    @142
    @159
    @8
    @161
    @150
    @40
    @1
    cH
    fveq2
    @142
    @136
    @91
    @160
    @23
    cdiv
    @144
    @40
    @1
    cG
    fveq2
    #
    oveq12d
    eqeq12d
    imbi12d
    @42
    @159
    @153
    @161
    @42
    @41
    @153
    cc
    wcel
    @159
    @153
    wceq
    @145
    @157
    vx
    cA
    @153
    cc
    cH
    0ellimcdiv.h
    fvmpt2
    syl2anc
    @42
    cB
    @136
    cC
    @160
    cdiv
    @42
    @136
    cB
    @146
    eqcomd
    @42
    @160
    cC
    @42
    @41
    @155
    @160
    cC
    wceq
    @145
    0ellimcdiv.c
    vx
    cA
    cC
    @154
    cG
    0ellimcdiv.g
    fvmpt2
    syl2anc
    #
    eqcomd
    oveq12d
    eqtrd
    chvar
    eqtrd
    fveq2d
    syl2anc
    @149
    @17
    @59
    wa
    #
    @25
    @121
    @151
    @11
    clt
    wbr
    @149
    @17
    @59
    @17
    @57
    @109
    @59
    @2
    @25
    @121
    simp-6l
    @152
    jca
    @119
    @25
    @121
    simplr
    @148
    @121
    simpr
    @167
    @25
    wa
    #
    @121
    wa
    #
    @151
    @120
    @24
    cdiv
    co
    #
    @11
    clt
    @167
    @151
    @170
    wceq
    #
    @25
    @121
    wph
    @59
    @171
    @16
    @76
    @91
    @23
    @147
    @79
    @42
    @160
    cc0
    wne
    #
    wi
    @76
    @23
    cc0
    wne
    #
    wi
    vx
    vv
    @76
    @173
    vx
    @139
    vx
    @23
    cc0
    @164
    vx
    cc0
    nfcv
    nfne
    nfim
    @142
    @42
    @76
    @172
    @173
    @143
    @142
    @160
    @23
    cc0
    @165
    neeq1d
    imbi12d
    @42
    @160
    cC
    cc0
    @166
    @156
    eqnetrd
    chvar
    #
    absdivd
    adantlr
    ad2antrr
    @169
    @170
    @94
    @24
    cdiv
    co
    #
    @11
    @167
    @170
    cr
    wcel
    #
    @25
    @121
    wph
    @59
    @176
    @16
    @76
    @120
    @24
    @76
    @91
    @147
    abscld
    #
    @86
    @76
    @23
    @79
    @174
    absne0d
    #
    redivcld
    adantlr
    ad2antrr
    @169
    @94
    @24
    @167
    @94
    cr
    wcel
    @25
    @121
    @167
    @11
    @22
    @16
    @11
    cr
    wcel
    #
    wph
    @59
    @11
    rpre
    ad2antlr
    #
    wph
    @22
    cr
    wcel
    #
    @16
    @59
    wph
    @22
    @55
    rpred
    #
    ad2antrr
    #
    remulcld
    ad2antrr
    #
    @167
    @24
    crp
    wcel
    #
    @25
    @121
    wph
    @59
    @185
    @16
    @76
    @23
    @79
    @174
    absrpcld
    #
    adantlr
    #
    ad2antrr
    #
    rerpdivcld
    @167
    @179
    @25
    @121
    @180
    ad2antrr
    @169
    @120
    @94
    @24
    @169
    wph
    @59
    @120
    cr
    wcel
    wph
    @16
    @59
    @25
    @121
    simp-4l
    @17
    @59
    @25
    @121
    simpllr
    @177
    syl2anc
    @184
    @188
    @168
    @121
    simpr
    ltdiv1dd
    @168
    @175
    @11
    clt
    wbr
    @121
    @168
    @175
    @11
    c1
    cmul
    co
    #
    @11
    clt
    @168
    @175
    @11
    @22
    @24
    cdiv
    co
    #
    cmul
    co
    #
    @189
    clt
    @167
    @175
    @191
    wceq
    @25
    @167
    @11
    @22
    @24
    @167
    @11
    @180
    recnd
    #
    wph
    @22
    cc
    wcel
    @16
    @59
    @71
    ad2antrr
    @167
    @24
    @187
    rpcnd
    wph
    @59
    @24
    cc0
    wne
    @16
    @178
    adantlr
    divassd
    adantr
    @168
    @190
    c1
    @11
    @167
    @190
    cr
    wcel
    @25
    @167
    @22
    @24
    @183
    @187
    rerpdivcld
    adantr
    @168
    1red
    wph
    @16
    @59
    @25
    simpllr
    wph
    @59
    @25
    @190
    c1
    clt
    wbr
    @16
    @76
    @25
    wa
    #
    @22
    c1
    @24
    wph
    @181
    @59
    @25
    @182
    ad2antrr
    c1
    crp
    wcel
    @193
    1rp
    a1i
    @76
    @185
    @25
    @186
    adantr
    @193
    @22
    c1
    cdiv
    co
    #
    @22
    @24
    clt
    wph
    @194
    @22
    wceq
    @59
    @25
    wph
    @22
    @71
    div1d
    ad2antrr
    @76
    @25
    simpr
    eqbrtrd
    ltdiv23d
    adantllr
    ltmul2dd
    eqbrtrd
    @167
    @189
    @11
    wceq
    @25
    @167
    @11
    @192
    mulid1d
    adantr
    breqtrd
    adantr
    lttrd
    eqbrtrd
    syl21anc
    eqbrtrd
    syl21anc
    3exp
    ralrimi
    @14
    @116
    vw
    @112
    crp
    @5
    @112
    wceq
    #
    @13
    @115
    vv
    cA
    @195
    @7
    @114
    @12
    @195
    @6
    @113
    @2
    @5
    @112
    @4
    clt
    breq2
    anbi2d
    imbi1d
    ralbidv
    rspcev
    syl2anc
    rexlimdv3a
    mpd
    rexlimdv3a
    mpd
    ralrimiva
    wph
    vy
    vw
    vv
    cA
    cE
    cc0
    cH
    @158
    @46
    @51
    ellimc3
    mpbir2and
end
