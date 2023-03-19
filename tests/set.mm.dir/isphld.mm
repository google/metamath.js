include "clvec.mm"
include "wcel.mm"
include "csca.mm"
include "cfv.mm"
include "csr.mm"
include "cbs.mm"
include "cv.mm"
include "cip.mm"
include "co.mm"
include "cmpt.mm"
include "crglmod.mm"
include "clmhm.mm"
include "c0g.mm"
include "wceq.mm"
include "wi.mm"
include "cstv.mm"
include "wral.mm"
include "w3a.mm"
include "cphl.mm"
include "eqeltrrd.mm"
include "wa.mm"
include "oveq1.mm"
include "cbvmptv.mm"
include "wf.mm"
include "cvsca.mm"
include "cplusg.mm"
include "cmulr.mm"
include "3expib.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "oveqd.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "eleq12d.mm"
include "3imtr3d.mm"
include "impl.mm"
include "an32s.mm"
include "fmptd.mm"
include "ralrimiva.mm"
include "weq.mm"
include "oveq2.mm"
include "mpteq2dv.mm"
include "feq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "eqidd.mm"
include "3exp.mm"
include "3anrot.mm"
include "3anbi123d.mm"
include "syl5bbr.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imp31.mm"
include "3exp2.mm"
include "impancom.mm"
include "3imp2.mm"
include "clss.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "adantr.mm"
include "eqid.mm"
include "lss1.mm"
include "lsscl.mm"
include "sylancom.mm"
include "ovex.mm"
include "fvmpt3i.mm"
include "simpr2.mm"
include "oveq2d.mm"
include "simpr3.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "ralrimivvva.mm"
include "wb.mm"
include "crg.mm"
include "lmodring.mm"
include "rlmlmod.mm"
include "3syl.mm"
include "rlmbas.mm"
include "cvv.mm"
include "fvex.mm"
include "rlmsca.mm"
include "ax-mp.mm"
include "rlmplusg.mm"
include "rlmvsca.mm"
include "islmhm2.mm"
include "syl2anc.mm"
include "mpbir3and.mm"
include "eleq1d.mm"
include "syl5eqel.mm"
include "eqeq2d.mm"
include "imp.mm"
include "fveq12d.mm"
include "expdimp.mm"
include "ralrimiv.mm"
include "3jca.mm"
include "isphl.mm"
include "syl3anbrc.mm"

theorem isphld
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.pl: class .+
  let c.pd: class .+^
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cI: class I
  let c.as: class .*
  let cK: class K
  let cO: class O
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vq: setvar q
  let vw: setvar w
  assume isphld.v: |- ( ph -> V = ( Base ` W ) )
  assume isphld.a: |- ( ph -> .+ = ( +g ` W ) )
  assume isphld.s: |- ( ph -> .x. = ( .s ` W ) )
  assume isphld.i: |- ( ph -> I = ( .i ` W ) )
  assume isphld.z: |- ( ph -> .0. = ( 0g ` W ) )
  assume isphld.f: |- ( ph -> F = ( Scalar ` W ) )
  assume isphld.k: |- ( ph -> K = ( Base ` F ) )
  assume isphld.p: |- ( ph -> .+^ = ( +g ` F ) )
  assume isphld.t: |- ( ph -> .X. = ( .r ` F ) )
  assume isphld.c: |- ( ph -> .* = ( *r ` F ) )
  assume isphld.o: |- ( ph -> O = ( 0g ` F ) )
  assume isphld.l: |- ( ph -> W e. LVec )
  assume isphld.r: |- ( ph -> F e. *Ring )
  assume isphld.cl: |- ( ( ph /\ x e. V /\ y e. V ) -> ( x I y ) e. K )
  assume isphld.d: |- ( ( ph /\ q e. K /\ ( x e. V /\ y e. V /\ z e. V ) ) -> ( ( ( q .x. x ) .+ y ) I z ) = ( ( q .X. ( x I z ) ) .+^ ( y I z ) ) )
  assume isphld.ns: |- ( ( ph /\ x e. V /\ ( x I x ) = O ) -> x = .0. )
  assume isphld.cj: |- ( ( ph /\ x e. V /\ y e. V ) -> ( .* ` ( x I y ) ) = ( y I x ) )

  disjoint q x
  disjoint q y
  disjoint q z
  disjoint ph q
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint W q
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint q w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint W w
  assert |- ( ph -> W e. PreHil )

  proof
    wph
    cW
    clvec
    wcel
    #
    cW
    csca
    cfv
    #
    csr
    wcel
    vy
    cW
    cbs
    cfv
    #
    vy
    cv
    #
    vx
    cv
    #
    cW
    cip
    cfv
    #
    co
    #
    cmpt
    #
    cW
    @1
    crglmod
    cfv
    #
    clmhm
    co
    #
    wcel
    #
    @4
    @4
    @5
    co
    #
    @1
    c0g
    cfv
    #
    wceq
    #
    @4
    cW
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    @4
    @3
    @5
    co
    #
    @1
    cstv
    cfv
    #
    cfv
    #
    @6
    wceq
    #
    vy
    @2
    wral
    #
    w3a
    #
    vx
    @2
    wral
    cW
    cphl
    wcel
    isphld.l
    wph
    cF
    @1
    csr
    isphld.f
    isphld.r
    eqeltrrd
    wph
    @22
    vx
    @2
    wph
    @4
    @2
    wcel
    #
    wa
    #
    @10
    @16
    @21
    @24
    @7
    vw
    @2
    vw
    cv
    #
    @4
    @5
    co
    #
    cmpt
    #
    @9
    vy
    vw
    @2
    @6
    @26
    @3
    @25
    @4
    @5
    oveq1
    cbvmptv
    wph
    vw
    @2
    @25
    vz
    cv
    #
    @5
    co
    #
    cmpt
    #
    @9
    wcel
    #
    vz
    @2
    wral
    @23
    @27
    @9
    wcel
    #
    wph
    @31
    vz
    @2
    wph
    @28
    @2
    wcel
    #
    wa
    #
    @31
    @2
    @1
    cbs
    cfv
    #
    @30
    wf
    #
    @1
    @1
    wceq
    #
    vq
    cv
    #
    @4
    cW
    cvsca
    cfv
    #
    co
    #
    @3
    cW
    cplusg
    cfv
    #
    co
    #
    @30
    cfv
    #
    @38
    @4
    @30
    cfv
    #
    @1
    cmulr
    cfv
    #
    co
    #
    @3
    @30
    cfv
    #
    @1
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vy
    @2
    wral
    vx
    @2
    wral
    vq
    @35
    wral
    #
    wph
    @2
    @35
    vw
    @2
    @25
    @3
    @5
    co
    #
    cmpt
    #
    wf
    #
    vy
    @2
    wral
    @33
    @36
    wph
    @54
    vy
    @2
    wph
    @3
    @2
    wcel
    #
    wa
    vx
    @2
    @17
    @35
    @53
    wph
    @23
    @55
    @17
    @35
    wcel
    #
    wph
    @23
    @55
    @56
    wph
    @4
    cV
    wcel
    #
    @3
    cV
    wcel
    #
    wa
    #
    @4
    @3
    cI
    co
    #
    cK
    wcel
    #
    @23
    @55
    wa
    #
    @56
    wph
    @57
    @58
    @61
    isphld.cl
    3expib
    wph
    @57
    @23
    @58
    @55
    wph
    cV
    @2
    @4
    isphld.v
    eleq2d
    #
    wph
    cV
    @2
    @3
    isphld.v
    eleq2d
    #
    anbi12d
    #
    wph
    @60
    @17
    cK
    @35
    wph
    cI
    @5
    @4
    @3
    isphld.i
    oveqd
    #
    wph
    cK
    cF
    cbs
    cfv
    @35
    isphld.k
    wph
    cF
    @1
    cbs
    isphld.f
    fveq2d
    eqtrd
    #
    eleq12d
    3imtr3d
    impl
    an32s
    vw
    vx
    @2
    @52
    @17
    @25
    @4
    @3
    @5
    oveq1
    cbvmptv
    fmptd
    ralrimiva
    @54
    @36
    vy
    @28
    @2
    vy
    vz
    weq
    #
    @2
    @35
    @53
    @30
    @68
    vw
    @2
    @52
    @29
    @3
    @28
    @25
    @5
    oveq2
    mpteq2dv
    feq1d
    rspccva
    sylan
    @34
    @1
    eqidd
    @34
    @50
    vq
    vx
    vy
    @35
    @2
    @2
    @34
    @38
    @35
    wcel
    #
    @23
    @55
    w3a
    #
    wa
    #
    @42
    @28
    @5
    co
    #
    @38
    @4
    @28
    @5
    co
    #
    @45
    co
    #
    @3
    @28
    @5
    co
    #
    @48
    co
    #
    @43
    @49
    @34
    @69
    @23
    @55
    @72
    @76
    wceq
    #
    wph
    @69
    @33
    @23
    @55
    @77
    wi
    wi
    wph
    @69
    wa
    @33
    @23
    @55
    @77
    wph
    @69
    @33
    @23
    @55
    w3a
    #
    @77
    wph
    @38
    cK
    wcel
    #
    @57
    @58
    @28
    cV
    wcel
    #
    w3a
    #
    @38
    @4
    c.x
    co
    #
    @3
    c.pl
    co
    #
    @28
    cI
    co
    #
    @38
    @4
    @28
    cI
    co
    #
    c.xp
    co
    #
    @3
    @28
    cI
    co
    #
    c.pd
    co
    #
    wceq
    #
    wi
    @69
    @78
    @77
    wi
    wph
    @79
    @81
    @89
    isphld.d
    3exp
    wph
    cK
    @35
    @38
    @67
    eleq2d
    wph
    @81
    @78
    @89
    @77
    @81
    @80
    @57
    @58
    w3a
    wph
    @78
    @80
    @57
    @58
    3anrot
    wph
    @80
    @33
    @57
    @23
    @58
    @55
    wph
    cV
    @2
    @28
    isphld.v
    eleq2d
    @63
    @64
    3anbi123d
    syl5bbr
    wph
    @84
    @72
    @88
    @76
    wph
    @83
    @42
    @28
    @28
    cI
    @5
    isphld.i
    wph
    @82
    @40
    @3
    @3
    c.pl
    @41
    isphld.a
    wph
    c.x
    @39
    @38
    @4
    isphld.s
    oveqd
    wph
    @3
    eqidd
    oveq123d
    wph
    @28
    eqidd
    oveq123d
    wph
    @86
    @74
    @87
    @75
    c.pd
    @48
    wph
    c.pd
    cF
    cplusg
    cfv
    @48
    isphld.p
    wph
    cF
    @1
    cplusg
    isphld.f
    fveq2d
    eqtrd
    wph
    @38
    @38
    @85
    @73
    c.xp
    @45
    wph
    c.xp
    cF
    cmulr
    cfv
    @45
    isphld.t
    wph
    cF
    @1
    cmulr
    isphld.f
    fveq2d
    eqtrd
    wph
    @38
    eqidd
    wph
    cI
    @5
    @4
    @28
    isphld.i
    oveqd
    oveq123d
    wph
    cI
    @5
    @3
    @28
    isphld.i
    oveqd
    oveq123d
    eqeq12d
    imbi12d
    3imtr3d
    imp31
    3exp2
    impancom
    3imp2
    @71
    @42
    @2
    wcel
    #
    @43
    @72
    wceq
    @34
    @70
    @2
    cW
    clss
    cfv
    #
    wcel
    #
    @90
    @71
    cW
    clmod
    wcel
    #
    @92
    @34
    @93
    @70
    wph
    @93
    @33
    wph
    @0
    @93
    isphld.l
    cW
    lveclmod
    syl
    #
    adantr
    #
    adantr
    @91
    @2
    cW
    @2
    eqid
    #
    @91
    eqid
    #
    lss1
    syl
    @35
    @41
    @91
    @39
    @2
    @1
    cW
    @4
    @3
    @38
    @1
    eqid
    #
    @35
    eqid
    #
    @41
    eqid
    #
    @39
    eqid
    #
    @97
    lsscl
    sylancom
    vw
    @42
    @29
    @72
    @2
    @30
    @25
    @42
    @28
    @5
    oveq1
    @30
    eqid
    #
    @25
    @28
    @5
    ovex
    #
    fvmpt3i
    syl
    @71
    @46
    @74
    @47
    @75
    @48
    @71
    @44
    @73
    @38
    @45
    @71
    @23
    @44
    @73
    wceq
    @34
    @69
    @23
    @55
    simpr2
    vw
    @4
    @29
    @73
    @2
    @30
    @25
    @4
    @28
    @5
    oveq1
    @102
    @103
    fvmpt3i
    syl
    oveq2d
    @71
    @55
    @47
    @75
    wceq
    @34
    @69
    @23
    @55
    simpr3
    vw
    @3
    @29
    @75
    @2
    @30
    @25
    @3
    @28
    @5
    oveq1
    @102
    @103
    fvmpt3i
    syl
    oveq12d
    3eqtr4d
    ralrimivvva
    @34
    @93
    @8
    clmod
    wcel
    #
    @31
    @36
    @37
    @51
    w3a
    wb
    @95
    wph
    @104
    @33
    wph
    @93
    @1
    crg
    wcel
    @104
    @94
    @1
    cW
    @98
    lmodring
    @1
    rlmlmod
    3syl
    adantr
    vq
    vx
    vy
    @2
    @35
    @41
    @48
    cW
    @8
    @39
    @45
    @35
    @30
    @1
    @1
    @96
    @1
    rlmbas
    @98
    @1
    cvv
    wcel
    @1
    @8
    csca
    cfv
    wceq
    cW
    csca
    fvex
    @1
    cvv
    rlmsca
    ax-mp
    @99
    @100
    @1
    rlmplusg
    @101
    @1
    rlmvsca
    islmhm2
    syl2anc
    mpbir3and
    ralrimiva
    @31
    @32
    vz
    @4
    @2
    vz
    vx
    weq
    #
    @30
    @27
    @9
    @105
    vw
    @2
    @29
    @26
    @28
    @4
    @25
    @5
    oveq2
    mpteq2dv
    eleq1d
    rspccva
    sylan
    syl5eqel
    wph
    @23
    @16
    wph
    @57
    @4
    @4
    cI
    co
    #
    cO
    wceq
    #
    @4
    c.0
    wceq
    #
    wi
    @23
    @16
    wph
    @57
    @107
    @108
    isphld.ns
    3exp
    @63
    wph
    @107
    @13
    @108
    @15
    wph
    @106
    @11
    cO
    @12
    wph
    cI
    @5
    @4
    @4
    isphld.i
    oveqd
    wph
    cO
    cF
    c0g
    cfv
    @12
    isphld.o
    wph
    cF
    @1
    c0g
    isphld.f
    fveq2d
    eqtrd
    eqeq12d
    wph
    c.0
    @14
    @4
    isphld.z
    eqeq2d
    imbi12d
    3imtr3d
    imp
    @24
    @20
    vy
    @2
    wph
    @23
    @55
    @20
    wph
    @59
    @60
    c.as
    cfv
    #
    @3
    @4
    cI
    co
    #
    wceq
    #
    @62
    @20
    wph
    @57
    @58
    @111
    isphld.cj
    3expib
    @65
    wph
    @109
    @19
    @110
    @6
    wph
    @60
    @17
    c.as
    @18
    wph
    c.as
    cF
    cstv
    cfv
    @18
    isphld.c
    wph
    cF
    @1
    cstv
    isphld.f
    fveq2d
    eqtrd
    @66
    fveq12d
    wph
    cI
    @5
    @3
    @4
    isphld.i
    oveqd
    eqeq12d
    3imtr3d
    expdimp
    ralrimiv
    3jca
    ralrimiva
    vx
    vy
    @1
    @5
    @18
    @2
    cW
    @14
    @12
    @96
    @98
    @5
    eqid
    @14
    eqid
    @18
    eqid
    @12
    eqid
    isphl
    syl3anbrc
end
