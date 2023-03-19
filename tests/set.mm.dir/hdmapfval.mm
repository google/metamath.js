include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "cun.mm"
include "wn.mm"
include "cotp.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "cmpt.mm"
include "clspn.mm"
include "chvm.mm"
include "clcd.mm"
include "cbs.mm"
include "chdma1.mm"
include "wsbc.mm"
include "cdvh.mm"
include "cid.mm"
include "cres.mm"
include "cltrn.mm"
include "cop.mm"
include "cab.mm"
include "chdma.mm"
include "hdmapffval.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "fveq2.mm"
include "reseq2d.mm"
include "opeq2d.mm"
include "fveq2d.mm"
include "oteq2d.mm"
include "eqeq2d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "riotaeqbidv.mm"
include "mpteq2dv.mm"
include "eleq2d.mm"
include "sbceqbid.mm"
include "sbcbidv.mm"
include "opex.mm"
include "fvex.mm"
include "w3a.mm"
include "wb.mm"
include "simp1.mm"
include "syl6eqr.mm"
include "simp2.mm"
include "simp3.mm"
include "eqtrd.mm"
include "id.mm"
include "fveq1.mm"
include "riotabidv.mm"
include "syl.mm"
include "sbcie.mm"
include "fveq2i.mm"
include "eqtr2i.mm"
include "a1i.mm"
include "sneqd.mm"
include "fveq12d.mm"
include "uneq12d.mm"
include "notbid.mm"
include "oteq1d.mm"
include "fveq1i.mm"
include "imbi12d.mm"
include "raleqbidv.mm"
include "mpteq12dv.mm"
include "syl5bb.mm"
include "syl3anc.mm"
include "sbc3ie.mm"
include "syl6bb.mm"
include "abbi1dv.mm"
include "eqid.mm"
include "cvv.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem hdmapfval
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cC: class C
  let cD: class D
  let cS: class S
  let cU: class U
  let cE: class E
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vw: setvar w
  let va: setvar a
  let ve: setvar e
  let vi: setvar i
  let vu: setvar u
  let vv: setvar v
  assume hdmapval.h: |- H = ( LHyp ` K )
  assume hdmapfval.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmapfval.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapfval.v: |- V = ( Base ` U )
  assume hdmapfval.n: |- N = ( LSpan ` U )
  assume hdmapfval.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmapfval.d: |- D = ( Base ` C )
  assume hdmapfval.j: |- J = ( ( HVMap ` K ) ` W )
  assume hdmapfval.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmapfval.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapfval.k: |- ( ph -> ( K e. A /\ W e. H ) )

  disjoint t y
  disjoint t z
  disjoint K t
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint D y
  disjoint E t
  disjoint E y
  disjoint E z
  disjoint I t
  disjoint I y
  disjoint I z
  disjoint U t
  disjoint U y
  disjoint U z
  disjoint V t
  disjoint V y
  disjoint V z
  disjoint W t
  disjoint W y
  disjoint W z
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint a e
  disjoint a i
  disjoint a k
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint K a
  disjoint e i
  disjoint e k
  disjoint e t
  disjoint e u
  disjoint e v
  disjoint e w
  disjoint e y
  disjoint e z
  disjoint K e
  disjoint i k
  disjoint i t
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i y
  disjoint i z
  disjoint K i
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k y
  disjoint k z
  disjoint K k
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint K u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint K v
  disjoint w y
  disjoint w z
  disjoint K w
  disjoint D a
  disjoint D e
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint E a
  disjoint E e
  disjoint E u
  disjoint E v
  disjoint E w
  disjoint I a
  disjoint I e
  disjoint I i
  disjoint I u
  disjoint I v
  disjoint I w
  disjoint J a
  disjoint J e
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint N a
  disjoint N e
  disjoint N u
  disjoint N v
  disjoint N w
  disjoint V a
  disjoint V e
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint W a
  disjoint W e
  disjoint W i
  disjoint W u
  disjoint W v
  disjoint W w
  assert |- ( ph -> S = ( t e. V |-> ( iota_ y e. D A. z e. V ( -. z e. ( ( N ` { E } ) u. ( N ` { t } ) ) -> y = ( I ` <. z , ( I ` <. E , ( J ` E ) , z >. ) , t >. ) ) ) ) )

  proof
    wph
    cK
    cA
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    cS
    vt
    cV
    vz
    cv
    #
    cE
    csn
    #
    cN
    cfv
    #
    vt
    cv
    #
    csn
    #
    cN
    cfv
    #
    cun
    #
    wcel
    #
    wn
    #
    vy
    cv
    #
    @2
    cE
    cE
    cJ
    cfv
    #
    @2
    cotp
    #
    cI
    cfv
    #
    @5
    cotp
    #
    cI
    cfv
    #
    wceq
    #
    wi
    #
    vz
    cV
    wral
    #
    vy
    cD
    crio
    #
    cmpt
    #
    wceq
    hdmapfval.k
    @0
    @1
    cS
    cW
    vw
    cH
    va
    cv
    #
    vt
    vv
    cv
    #
    @2
    ve
    cv
    #
    csn
    #
    vu
    cv
    #
    clspn
    cfv
    #
    cfv
    #
    @6
    @27
    cfv
    #
    cun
    #
    wcel
    #
    wn
    #
    @11
    @2
    @24
    @24
    vw
    cv
    #
    cK
    chvm
    cfv
    #
    cfv
    #
    cfv
    #
    @2
    cotp
    #
    vi
    cv
    #
    cfv
    #
    @5
    cotp
    #
    @38
    cfv
    #
    wceq
    #
    wi
    #
    vz
    @23
    wral
    #
    vy
    @33
    cK
    clcd
    cfv
    #
    cfv
    #
    cbs
    cfv
    #
    crio
    #
    cmpt
    #
    wcel
    #
    vi
    @33
    cK
    chdma1
    cfv
    #
    cfv
    #
    wsbc
    #
    vv
    @26
    cbs
    cfv
    #
    wsbc
    #
    vu
    @33
    cK
    cdvh
    cfv
    #
    cfv
    #
    wsbc
    #
    ve
    cid
    cK
    cbs
    cfv
    cres
    #
    cid
    @33
    cK
    cltrn
    cfv
    #
    cfv
    #
    cres
    #
    cop
    #
    wsbc
    #
    va
    cab
    #
    cmpt
    #
    cfv
    #
    @21
    @0
    cS
    cW
    cK
    chdma
    cfv
    #
    cfv
    @67
    hdmapfval.s
    @0
    cW
    @68
    @66
    vy
    vz
    vw
    vv
    vu
    vt
    ve
    vi
    cH
    cK
    cA
    va
    hdmapval.h
    hdmapffval
    fveq1d
    syl5eq
    vw
    cW
    @65
    @21
    cH
    @66
    @33
    cW
    wceq
    #
    @64
    va
    @21
    @69
    @64
    @22
    vt
    @23
    @32
    @11
    @2
    @24
    @24
    cW
    @34
    cfv
    #
    cfv
    #
    @2
    cotp
    #
    @38
    cfv
    #
    @5
    cotp
    #
    @38
    cfv
    #
    wceq
    #
    wi
    #
    vz
    @23
    wral
    #
    vy
    cW
    @45
    cfv
    #
    cbs
    cfv
    #
    crio
    #
    cmpt
    #
    wcel
    #
    vi
    cW
    @51
    cfv
    #
    wsbc
    #
    vv
    @54
    wsbc
    #
    vu
    cW
    @56
    cfv
    #
    wsbc
    #
    ve
    @59
    cid
    cW
    @60
    cfv
    #
    cres
    #
    cop
    #
    wsbc
    @22
    @21
    wcel
    #
    @69
    @58
    @88
    ve
    @63
    @91
    @69
    @62
    @90
    @59
    @69
    @61
    @89
    cid
    @33
    cW
    @60
    fveq2
    reseq2d
    opeq2d
    @69
    @55
    @86
    vu
    @57
    @87
    @33
    cW
    @56
    fveq2
    @69
    @53
    @85
    vv
    @54
    @69
    @50
    @83
    vi
    @52
    @84
    @33
    cW
    @51
    fveq2
    @69
    @49
    @82
    @22
    @69
    vt
    @23
    @48
    @81
    @69
    @44
    @78
    vy
    @47
    @80
    @69
    @46
    @79
    cbs
    @33
    cW
    @45
    fveq2
    fveq2d
    @69
    @43
    @77
    vz
    @23
    @69
    @42
    @76
    @32
    @69
    @41
    @75
    @11
    @69
    @40
    @74
    @38
    @69
    @39
    @73
    @2
    @5
    @69
    @37
    @72
    @38
    @69
    @36
    @71
    @24
    @2
    @69
    @24
    @35
    @70
    @33
    cW
    @34
    fveq2
    fveq1d
    oteq2d
    fveq2d
    oteq2d
    fveq2d
    eqeq2d
    imbi2d
    ralbidv
    riotaeqbidv
    mpteq2dv
    eleq2d
    sbceqbid
    sbcbidv
    sbceqbid
    sbceqbid
    @85
    @92
    ve
    vu
    vv
    @91
    @87
    @54
    @59
    @90
    opex
    cW
    @56
    fvex
    @26
    cbs
    fvex
    @24
    @91
    wceq
    #
    @26
    @87
    wceq
    #
    @23
    @54
    wceq
    #
    w3a
    #
    @24
    cE
    wceq
    #
    @26
    cU
    wceq
    #
    @23
    cV
    wceq
    #
    @85
    @92
    wb
    @96
    @24
    @91
    cE
    @93
    @94
    @95
    simp1
    hdmapfval.e
    syl6eqr
    @96
    @26
    @87
    cU
    @93
    @94
    @95
    simp2
    hdmapfval.u
    syl6eqr
    #
    @96
    @23
    cU
    cbs
    cfv
    #
    cV
    @96
    @23
    @54
    @101
    @93
    @94
    @95
    simp3
    @96
    @26
    cU
    cbs
    @100
    fveq2d
    eqtrd
    hdmapfval.v
    syl6eqr
    @85
    @22
    vt
    @23
    @32
    @11
    @2
    @72
    cI
    cfv
    #
    @5
    cotp
    #
    cI
    cfv
    #
    wceq
    #
    wi
    #
    vz
    @23
    wral
    #
    vy
    @80
    crio
    #
    cmpt
    #
    wcel
    #
    @97
    @98
    @99
    w3a
    #
    @92
    @83
    @110
    vi
    @84
    cW
    @51
    fvex
    @38
    @84
    wceq
    #
    @38
    cI
    wceq
    #
    @83
    @110
    wb
    @112
    @38
    @84
    cI
    @112
    id
    hdmapfval.i
    syl6eqr
    @113
    @82
    @109
    @22
    @113
    vt
    @23
    @81
    @108
    @113
    @78
    @107
    vy
    @80
    @113
    @77
    @106
    vz
    @23
    @113
    @76
    @105
    @32
    @113
    @75
    @104
    @11
    @113
    @75
    @74
    cI
    cfv
    @104
    @74
    @38
    cI
    fveq1
    @113
    @74
    @103
    cI
    @113
    @73
    @102
    @2
    @5
    @72
    @38
    cI
    fveq1
    oteq2d
    fveq2d
    eqtrd
    eqeq2d
    imbi2d
    ralbidv
    riotabidv
    mpteq2dv
    eleq2d
    syl
    sbcie
    @111
    @109
    @21
    @22
    @111
    vt
    @23
    @108
    cV
    @20
    @97
    @98
    @99
    simp3
    #
    @111
    @107
    @19
    vy
    @80
    cD
    @80
    cD
    wceq
    @111
    cD
    cC
    cbs
    cfv
    @80
    hdmapfval.d
    cC
    @79
    cbs
    hdmapfval.c
    fveq2i
    eqtr2i
    a1i
    @111
    @106
    @18
    vz
    @23
    cV
    @114
    @111
    @32
    @10
    @105
    @17
    @111
    @31
    @9
    @111
    @30
    @8
    @2
    @111
    @28
    @4
    @29
    @7
    @111
    @25
    @3
    @27
    cN
    @111
    @27
    cU
    clspn
    cfv
    cN
    @111
    @26
    cU
    clspn
    @97
    @98
    @99
    simp2
    fveq2d
    hdmapfval.n
    syl6eqr
    #
    @111
    @24
    cE
    @97
    @98
    @99
    simp1
    #
    sneqd
    fveq12d
    @111
    @6
    @27
    cN
    @115
    fveq1d
    uneq12d
    eleq2d
    notbid
    @111
    @104
    @16
    @11
    @111
    @103
    @15
    cI
    @111
    @102
    @14
    @2
    @5
    @111
    @72
    @13
    cI
    @111
    @72
    cE
    @71
    @2
    cotp
    @13
    @111
    @24
    cE
    @71
    @2
    @116
    oteq1d
    @111
    @71
    @12
    cE
    @2
    @111
    @71
    cE
    @70
    cfv
    @12
    @111
    @24
    cE
    @70
    @116
    fveq2d
    cE
    cJ
    @70
    hdmapfval.j
    fveq1i
    syl6eqr
    oteq2d
    eqtrd
    fveq2d
    oteq2d
    fveq2d
    eqeq2d
    imbi12d
    raleqbidv
    riotaeqbidv
    mpteq12dv
    eleq2d
    syl5bb
    syl3anc
    sbc3ie
    syl6bb
    abbi1dv
    @66
    eqid
    vt
    cV
    @20
    cV
    @101
    cvv
    hdmapfval.v
    cU
    cbs
    fvex
    eqeltri
    mptex
    fvmpt
    sylan9eq
    syl
end
