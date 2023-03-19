include "cicc.mm"
include "co.mm"
include "cc.mm"
include "ccncf.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "ftc1lem2.mm"
include "wa.mm"
include "wss.mm"
include "cvol.mm"
include "citg.mm"
include "cdm.mm"
include "cvv.mm"
include "fvexd.mm"
include "cmpt.mm"
include "cibl.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "adantr.mm"
include "simpr.mm"
include "itgcn.mm"
include "weq.mm"
include "wb.mm"
include "oveq12.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "fveq2.mm"
include "oveqan12d.mm"
include "imbi12d.mm"
include "ancoms.mm"
include "cr.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "ad2antrr.mm"
include "ad3antrrr.mm"
include "simprr.mm"
include "sseldd.mm"
include "recnd.mm"
include "simprl.mm"
include "abssubd.mm"
include "ffvelrnd.mm"
include "cle.mm"
include "w3a.mm"
include "cioo.mm"
include "wceq.mm"
include "simpr3.mm"
include "simpr1.mm"
include "simpr2.mm"
include "ftc1lem1.mm"
include "mpdan.mm"
include "adantlr.mm"
include "ad2ant2r.mm"
include "cxr.mm"
include "rexrd.mm"
include "simprl1.mm"
include "elicc2.mm"
include "mpbid.mm"
include "simp2d.mm"
include "iooss1.mm"
include "simprl2.mm"
include "simp3d.mm"
include "iooss2.mm"
include "sstrd.mm"
include "ioombl.mm"
include "a1i.mm"
include "iblss.mm"
include "itgcl.mm"
include "abscld.mm"
include "cmbf.mm"
include "iblmbf.mm"
include "syl.mm"
include "mbfmptcl.mm"
include "iblabs.mm"
include "itgrecl.mm"
include "rpred.mm"
include "itgabs.mm"
include "simplr.mm"
include "covol.mm"
include "mblvol.mm"
include "ax-mp.mm"
include "ioossre.mm"
include "ovolcl.mm"
include "mp1i.mm"
include "simp1d.mm"
include "resubcld.mm"
include "rpxrd.mm"
include "ioossicc.mm"
include "ovolss.mm"
include "sylancr.mm"
include "simprl3.mm"
include "ovolicc.mm"
include "syl3anc.mm"
include "breqtrd.mm"
include "abssubge0d.mm"
include "eqbrtrrd.mm"
include "xrlelttrd.mm"
include "syl5eqbr.mm"
include "jca.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "cbvitgv.mm"
include "itgeq1.mm"
include "syl5eq.mm"
include "rspcv.mm"
include "syl3c.mm"
include "lelttrd.mm"
include "eqbrtrd.mm"
include "expr.mm"
include "wlogle.mm"
include "ralrimivva.mm"
include "ex.mm"
include "anassrs.mm"
include "reximdva.mm"
include "mpd.mm"
include "r19.12.mm"
include "ralrimiva.mm"
include "ralcom.mm"
include "sylib.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "ssid.mm"
include "elcncf2.mm"
include "sylancl.mm"
include "mpbir2and.mm"

theorem ftc1a
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cF: class F
  let cG: class G
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let vd: setvar d
  let vr: setvar r
  let ve: setvar e
  let cX: class X
  let cE: class E
  let cH: class H
  let cY: class Y
  let cL: class L
  let cR: class R
  assume ftc1.g: |- G = ( x e. ( A [,] B ) |-> S. ( A (,) x ) ( F ` t ) _d t )
  assume ftc1.a: |- ( ph -> A e. RR )
  assume ftc1.b: |- ( ph -> B e. RR )
  assume ftc1.le: |- ( ph -> A <_ B )
  assume ftc1.s: |- ( ph -> ( A (,) B ) C_ D )
  assume ftc1.d: |- ( ph -> D C_ RR )
  assume ftc1.i: |- ( ph -> F e. L^1 )
  assume ftc1a.f: |- ( ph -> F : D --> CC )

  disjoint t x
  disjoint D t
  disjoint D x
  disjoint A t
  disjoint A x
  disjoint B t
  disjoint B x
  disjoint ph t
  disjoint ph x
  disjoint F t
  disjoint F x
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint C s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint C t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint C u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint C v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint d r
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint D d
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint D r
  disjoint D s
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D y
  disjoint D z
  disjoint d e
  disjoint G d
  disjoint e r
  disjoint e s
  disjoint e u
  disjoint e y
  disjoint e z
  disjoint G e
  disjoint G r
  disjoint G s
  disjoint G u
  disjoint G y
  disjoint G z
  disjoint A d
  disjoint e t
  disjoint e v
  disjoint e w
  disjoint e x
  disjoint A e
  disjoint A r
  disjoint A s
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint B d
  disjoint B e
  disjoint B r
  disjoint B s
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint X t
  disjoint X x
  disjoint X z
  disjoint E t
  disjoint E y
  disjoint H s
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H y
  disjoint d ph
  disjoint e ph
  disjoint ph r
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint Y t
  disjoint Y x
  disjoint F d
  disjoint F r
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint L s
  disjoint L u
  disjoint L v
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint R y
  assert |- ( ph -> G e. ( ( A [,] B ) -cn-> CC ) )

  proof
    wph
    cG
    cA
    cB
    cicc
    co
    #
    cc
    ccncf
    co
    wcel
    #
    @0
    cc
    cG
    wf
    #
    vz
    cv
    #
    vy
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vd
    cv
    #
    clt
    wbr
    #
    @3
    cG
    cfv
    #
    @4
    cG
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    ve
    cv
    #
    clt
    wbr
    #
    wi
    #
    vz
    @0
    wral
    #
    vd
    crp
    wrex
    #
    ve
    crp
    wral
    vy
    @0
    wral
    #
    wph
    vx
    vt
    cA
    cB
    cD
    cF
    cG
    ftc1.g
    ftc1.a
    ftc1.b
    ftc1.le
    ftc1.s
    ftc1.d
    ftc1.i
    ftc1a.f
    ftc1lem2
    #
    wph
    @17
    vy
    @0
    wral
    #
    ve
    crp
    wral
    @18
    wph
    @20
    ve
    crp
    wph
    @13
    crp
    wcel
    #
    wa
    #
    @16
    vy
    @0
    wral
    #
    vd
    crp
    wrex
    #
    @20
    @22
    vu
    cv
    #
    cD
    wss
    #
    @25
    cvol
    cfv
    #
    @7
    clt
    wbr
    #
    wa
    #
    vw
    @25
    vw
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    citg
    #
    @13
    clt
    wbr
    #
    wi
    #
    vu
    cvol
    cdm
    #
    wral
    #
    vd
    crp
    wrex
    @24
    @22
    vw
    vu
    cD
    @31
    @13
    cvv
    vd
    @22
    @30
    cD
    wcel
    wa
    @30
    cF
    fvexd
    wph
    vw
    cD
    @31
    cmpt
    #
    cibl
    wcel
    @21
    wph
    cF
    @38
    cibl
    wph
    vw
    cD
    cc
    cF
    ftc1a.f
    feqmptd
    ftc1.i
    eqeltrrd
    adantr
    wph
    @21
    simpr
    itgcn
    @22
    @37
    @23
    vd
    crp
    wph
    @21
    @7
    crp
    wcel
    #
    @37
    @23
    wi
    wph
    @21
    @39
    wa
    #
    wa
    #
    @37
    @23
    @41
    @37
    wa
    #
    @15
    vy
    vz
    @0
    @0
    @42
    vs
    cv
    #
    vr
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    @43
    cG
    cfv
    #
    @44
    cG
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @13
    clt
    wbr
    #
    wi
    #
    @15
    @4
    @3
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    @10
    @9
    cmin
    co
    #
    cabs
    cfv
    #
    @13
    clt
    wbr
    #
    wi
    #
    vy
    vz
    vr
    vs
    @0
    vs
    vz
    weq
    #
    vr
    vy
    weq
    #
    @53
    @15
    wb
    @61
    @62
    wa
    #
    @47
    @8
    @52
    @14
    @63
    @46
    @6
    @7
    clt
    @63
    @45
    @5
    cabs
    @43
    @3
    @44
    @4
    cmin
    oveq12
    fveq2d
    breq1d
    @63
    @51
    @12
    @13
    clt
    @63
    @50
    @11
    cabs
    @61
    @62
    @48
    @9
    @49
    @10
    cmin
    @43
    @3
    cG
    fveq2
    @44
    @4
    cG
    fveq2
    oveqan12d
    fveq2d
    breq1d
    imbi12d
    ancoms
    vs
    vy
    weq
    #
    vr
    vz
    weq
    #
    @53
    @60
    wb
    @64
    @65
    wa
    #
    @47
    @56
    @52
    @59
    @66
    @46
    @55
    @7
    clt
    @66
    @45
    @54
    cabs
    @43
    @4
    @44
    @3
    cmin
    oveq12
    fveq2d
    breq1d
    @66
    @51
    @58
    @13
    clt
    @66
    @50
    @57
    cabs
    @64
    @65
    @48
    @10
    @49
    @9
    cmin
    @43
    @4
    cG
    fveq2
    @44
    @3
    cG
    fveq2
    oveqan12d
    fveq2d
    breq1d
    imbi12d
    ancoms
    wph
    @0
    cr
    wss
    #
    @40
    @37
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @67
    ftc1.a
    ftc1.b
    cA
    cB
    iccssre
    syl2anc
    #
    ad2antrr
    @42
    @4
    @0
    wcel
    #
    @3
    @0
    wcel
    #
    wa
    #
    wa
    #
    @8
    @56
    @14
    @59
    @74
    @6
    @55
    @7
    clt
    @74
    @3
    @4
    @74
    @3
    @74
    @0
    cr
    @3
    wph
    @67
    @40
    @37
    @73
    @70
    ad3antrrr
    #
    @42
    @71
    @72
    simprr
    #
    sseldd
    recnd
    @74
    @4
    @74
    @0
    cr
    @4
    @75
    @42
    @71
    @72
    simprl
    #
    sseldd
    recnd
    abssubd
    breq1d
    @74
    @12
    @58
    @13
    clt
    @74
    @9
    @10
    @74
    @0
    cc
    @3
    cG
    wph
    @2
    @40
    @37
    @73
    @19
    ad3antrrr
    #
    @76
    ffvelrnd
    @74
    @0
    cc
    @4
    cG
    @78
    @77
    ffvelrnd
    abssubd
    breq1d
    imbi12d
    @42
    @71
    @72
    @4
    @3
    cle
    wbr
    #
    w3a
    #
    @8
    @14
    @42
    @80
    @8
    wa
    #
    wa
    #
    @12
    vt
    @4
    @3
    cioo
    co
    #
    vt
    cv
    #
    cF
    cfv
    #
    citg
    #
    cabs
    cfv
    #
    @13
    clt
    @82
    @11
    @86
    cabs
    @41
    @80
    @11
    @86
    wceq
    #
    @37
    @8
    wph
    @80
    @88
    @40
    wph
    @80
    wa
    #
    @79
    @88
    wph
    @71
    @72
    @79
    simpr3
    @89
    vx
    vt
    cA
    cB
    cD
    cF
    cG
    @4
    @3
    ftc1.g
    wph
    @68
    @80
    ftc1.a
    adantr
    wph
    @69
    @80
    ftc1.b
    adantr
    wph
    cA
    cB
    cle
    wbr
    @80
    ftc1.le
    adantr
    wph
    cA
    cB
    cioo
    co
    #
    cD
    wss
    #
    @80
    ftc1.s
    adantr
    wph
    cD
    cr
    wss
    @80
    ftc1.d
    adantr
    wph
    cF
    cibl
    wcel
    @80
    ftc1.i
    adantr
    wph
    cD
    cc
    cF
    wf
    @80
    ftc1a.f
    adantr
    wph
    @71
    @72
    @79
    simpr1
    wph
    @71
    @72
    @79
    simpr2
    ftc1lem1
    mpdan
    adantlr
    ad2ant2r
    fveq2d
    @82
    @87
    vt
    @83
    @85
    cabs
    cfv
    #
    citg
    #
    @13
    @82
    @86
    @82
    vt
    @83
    @85
    cvv
    @82
    @84
    @83
    wcel
    wa
    #
    @84
    cF
    fvexd
    #
    @82
    vt
    @83
    cD
    @85
    cvv
    @82
    @83
    @90
    cD
    @82
    @83
    cA
    @3
    cioo
    co
    #
    @90
    @82
    cA
    cxr
    wcel
    cA
    @4
    cle
    wbr
    #
    @83
    @96
    wss
    @82
    cA
    wph
    @68
    @40
    @37
    @81
    ftc1.a
    ad3antrrr
    #
    rexrd
    @82
    @4
    cr
    wcel
    #
    @97
    @4
    cB
    cle
    wbr
    #
    @82
    @71
    @99
    @97
    @100
    w3a
    #
    @71
    @72
    @79
    @8
    @42
    simprl1
    @82
    @68
    @69
    @71
    @101
    wb
    @98
    wph
    @69
    @40
    @37
    @81
    ftc1.b
    ad3antrrr
    #
    cA
    cB
    @4
    elicc2
    syl2anc
    mpbid
    #
    simp2d
    cA
    @4
    @3
    iooss1
    syl2anc
    @82
    cB
    cxr
    wcel
    @3
    cB
    cle
    wbr
    #
    @96
    @90
    wss
    @82
    cB
    @102
    rexrd
    @82
    @3
    cr
    wcel
    #
    cA
    @3
    cle
    wbr
    #
    @104
    @82
    @72
    @105
    @106
    @104
    w3a
    #
    @71
    @72
    @79
    @8
    @42
    simprl2
    @82
    @68
    @69
    @72
    @107
    wb
    @98
    @102
    cA
    cB
    @3
    elicc2
    syl2anc
    mpbid
    #
    simp3d
    cA
    @3
    cB
    iooss2
    syl2anc
    sstrd
    wph
    @91
    @40
    @37
    @81
    ftc1.s
    ad3antrrr
    sstrd
    #
    @83
    @36
    wcel
    #
    @82
    @4
    @3
    ioombl
    #
    a1i
    #
    @82
    @84
    cD
    wcel
    wa
    @84
    cF
    fvexd
    wph
    vt
    cD
    @85
    cmpt
    #
    cibl
    wcel
    @40
    @37
    @81
    wph
    cF
    @113
    cibl
    wph
    vt
    cD
    cc
    cF
    ftc1a.f
    feqmptd
    ftc1.i
    eqeltrrd
    ad3antrrr
    iblss
    #
    itgcl
    abscld
    @82
    vt
    @83
    @92
    @94
    @85
    @82
    vt
    @83
    @85
    cvv
    @82
    vt
    @83
    @85
    cmpt
    #
    cibl
    wcel
    @115
    cmbf
    wcel
    @114
    @115
    iblmbf
    syl
    @95
    mbfmptcl
    abscld
    @82
    vt
    @83
    @85
    cvv
    @95
    @114
    iblabs
    itgrecl
    @82
    @13
    @41
    @21
    @37
    @81
    wph
    @21
    @39
    simprl
    ad2antrr
    rpred
    @82
    vt
    @83
    @85
    cvv
    @95
    @114
    itgabs
    @82
    @110
    @37
    @83
    cD
    wss
    #
    @83
    cvol
    cfv
    #
    @7
    clt
    wbr
    #
    wa
    #
    @93
    @13
    clt
    wbr
    #
    @112
    @41
    @37
    @81
    simplr
    @82
    @116
    @118
    @109
    @82
    @117
    @83
    covol
    cfv
    #
    @7
    clt
    @110
    @117
    @121
    wceq
    @111
    @83
    mblvol
    ax-mp
    @82
    @121
    @5
    @7
    @83
    cr
    wss
    @121
    cxr
    wcel
    @82
    @4
    @3
    ioossre
    @83
    ovolcl
    mp1i
    @82
    @5
    @82
    @3
    @4
    @82
    @105
    @106
    @104
    @108
    simp1d
    #
    @82
    @99
    @97
    @100
    @103
    simp1d
    #
    resubcld
    rexrd
    @82
    @7
    @41
    @39
    @37
    @81
    wph
    @21
    @39
    simprr
    ad2antrr
    rpxrd
    @82
    @121
    @4
    @3
    cicc
    co
    #
    covol
    cfv
    #
    @5
    cle
    @82
    @83
    @124
    wss
    @124
    cr
    wss
    #
    @121
    @125
    cle
    wbr
    @4
    @3
    ioossicc
    @82
    @99
    @105
    @126
    @123
    @122
    @4
    @3
    iccssre
    syl2anc
    @83
    @124
    ovolss
    sylancr
    @82
    @99
    @105
    @79
    @125
    @5
    wceq
    @123
    @122
    @71
    @72
    @79
    @8
    @42
    simprl3
    #
    @4
    @3
    ovolicc
    syl3anc
    breqtrd
    @82
    @6
    @5
    @7
    clt
    @82
    @4
    @3
    @123
    @122
    @127
    abssubge0d
    @42
    @80
    @8
    simprr
    eqbrtrrd
    xrlelttrd
    syl5eqbr
    jca
    @35
    @119
    @120
    wi
    vu
    @83
    @36
    @25
    @83
    wceq
    #
    @29
    @119
    @34
    @120
    @128
    @26
    @116
    @28
    @118
    @25
    @83
    cD
    sseq1
    @128
    @27
    @117
    @7
    clt
    @25
    @83
    cvol
    fveq2
    breq1d
    anbi12d
    @128
    @33
    @93
    @13
    clt
    @128
    @33
    vt
    @25
    @92
    citg
    @93
    vw
    vt
    @25
    @32
    @92
    vw
    vt
    weq
    @31
    @85
    cabs
    @30
    @84
    cF
    fveq2
    fveq2d
    cbvitgv
    vt
    @25
    @83
    @92
    itgeq1
    syl5eq
    breq1d
    imbi12d
    rspcv
    syl3c
    lelttrd
    eqbrtrd
    expr
    wlogle
    ralrimivva
    ex
    anassrs
    reximdva
    mpd
    @16
    vd
    vy
    crp
    @0
    r19.12
    syl
    ralrimiva
    @17
    ve
    vy
    crp
    @0
    ralcom
    sylib
    wph
    @0
    cc
    wss
    cc
    cc
    wss
    @1
    @2
    @18
    wa
    wb
    wph
    @0
    cr
    cc
    @70
    ax-resscn
    syl6ss
    cc
    ssid
    vy
    ve
    vd
    vz
    @0
    cc
    cG
    elcncf2
    sylancl
    mpbir2and
end
