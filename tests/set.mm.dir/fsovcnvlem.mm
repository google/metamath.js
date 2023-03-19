include "ccom.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "crab.mm"
include "cmpt.mm"
include "cid.mm"
include "cres.mm"
include "wf.mm"
include "wss.mm"
include "ssrab2.mm"
include "a1i.mm"
include "sselpwd.mm"
include "adantr.mm"
include "eqid.mm"
include "fmptd.mm"
include "cvv.mm"
include "pwexg.mm"
include "syl.mm"
include "elmapd.mm"
include "mpbird.mm"
include "fsovd.mm"
include "syl5eq.mm"
include "cmpt2.mm"
include "weq.mm"
include "oveq2.mm"
include "rabeq.mm"
include "mpteq2dv.mm"
include "mpteq12dv.mm"
include "pweq.mm"
include "oveq1d.mm"
include "mpteq1.mm"
include "cbvmpt2v.mm"
include "fveq1.mm"
include "eleq2d.mm"
include "rabbidv.mm"
include "cbvmptv.mm"
include "eleq1.mm"
include "fveq2.mm"
include "cbvrabv.mm"
include "mpteq2i.mm"
include "eqtri.mm"
include "mpt2eq123i.mm"
include "3eqtri.mm"
include "wceq.mm"
include "fmptco.mm"
include "wa.mm"
include "eqidd.mm"
include "adantl.mm"
include "simpr.mm"
include "rabexg.mm"
include "ad2antrr.mm"
include "fvmptd.mm"
include "wb.mm"
include "elrab3.mm"
include "ad2antlr.mm"
include "bitrd.mm"
include "rabbidva.mm"
include "adantlr.mm"
include "cin.mm"
include "dfin5.mm"
include "elmapi.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "sseqin2.mm"
include "sylib.mm"
include "syl5reqr.mm"
include "eqtr4d.mm"
include "mpteq2dva.mm"
include "feqmptd.mm"
include "mptresid.mm"
include "3eqtrd.mm"

theorem fsovcnvlem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cG: class G
  let cH: class H
  let cO: class O
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vg: setvar g
  let vu: setvar u
  let vv: setvar v
  assume fsovd.fs: |- O = ( a e. _V , b e. _V |-> ( f e. ( ~P b ^m a ) |-> ( y e. b |-> { x e. a | y e. ( f ` x ) } ) ) )
  assume fsovd.a: |- ( ph -> A e. V )
  assume fsovd.b: |- ( ph -> B e. W )
  assume fsovfvd.g: |- G = ( A O B )
  assume fsovcnvlem.h: |- H = ( B O A )

  disjoint A a
  disjoint A b
  disjoint A f
  disjoint A x
  disjoint A y
  disjoint a b
  disjoint a f
  disjoint a x
  disjoint a y
  disjoint b f
  disjoint b x
  disjoint b y
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint B a
  disjoint B b
  disjoint B f
  disjoint B y
  disjoint a ph
  disjoint b ph
  disjoint f ph
  disjoint ph y
  disjoint A c
  disjoint A d
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint c f
  disjoint c x
  disjoint c y
  disjoint d f
  disjoint d x
  disjoint d y
  disjoint A g
  disjoint A u
  disjoint A v
  disjoint c g
  disjoint c u
  disjoint c v
  disjoint d g
  disjoint d u
  disjoint d v
  disjoint f g
  disjoint f u
  disjoint f v
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint B c
  disjoint B d
  disjoint B g
  disjoint B u
  disjoint B v
  disjoint c ph
  disjoint d ph
  disjoint ph u
  disjoint ph v
  assert |- ( ph -> ( H o. G ) = ( _I |` ( ~P B ^m A ) ) )

  proof
    wph
    cH
    cG
    ccom
    vf
    cB
    cpw
    #
    cA
    cmap
    co
    #
    vu
    cA
    vu
    cv
    #
    vv
    cv
    #
    vy
    cB
    vy
    cv
    #
    vx
    cv
    #
    vf
    cv
    #
    cfv
    #
    wcel
    #
    vx
    cA
    crab
    #
    cmpt
    #
    cfv
    #
    wcel
    #
    vv
    cB
    crab
    #
    cmpt
    #
    cmpt
    vf
    @1
    @6
    cmpt
    #
    cid
    @1
    cres
    #
    wph
    vf
    vg
    @1
    cA
    cpw
    #
    cB
    cmap
    co
    #
    @10
    vu
    cA
    @2
    @3
    vg
    cv
    #
    cfv
    #
    wcel
    #
    vv
    cB
    crab
    #
    cmpt
    #
    @14
    cG
    cH
    wph
    @10
    @18
    wcel
    #
    @6
    @1
    wcel
    #
    wph
    @24
    cB
    @17
    @10
    wf
    wph
    vy
    cB
    @9
    @17
    @10
    wph
    @9
    @17
    wcel
    @4
    cB
    wcel
    wph
    @9
    cA
    cV
    fsovd.a
    @9
    cA
    wss
    wph
    @8
    vx
    cA
    ssrab2
    a1i
    sselpwd
    adantr
    @10
    eqid
    fmptd
    wph
    @17
    cB
    @10
    cvv
    cW
    wph
    cA
    cV
    wcel
    #
    @17
    cvv
    wcel
    fsovd.a
    cA
    cV
    pwexg
    syl
    fsovd.b
    elmapd
    mpbird
    adantr
    wph
    cG
    cA
    cB
    cO
    co
    vf
    @1
    @10
    cmpt
    fsovfvd.g
    wph
    vx
    vy
    cA
    cB
    vf
    cO
    cV
    cW
    va
    vb
    fsovd.fs
    fsovd.a
    fsovd.b
    fsovd
    syl5eq
    wph
    cH
    cB
    cA
    cO
    co
    vg
    @18
    @23
    cmpt
    fsovcnvlem.h
    wph
    vv
    vu
    cB
    cA
    vg
    cO
    cW
    cV
    vd
    vc
    cO
    va
    vb
    cvv
    cvv
    vf
    vb
    cv
    #
    cpw
    #
    va
    cv
    #
    cmap
    co
    #
    vy
    @27
    @8
    vx
    @29
    crab
    #
    cmpt
    #
    cmpt
    #
    cmpt2
    vd
    vc
    cvv
    cvv
    vf
    vc
    cv
    #
    cpw
    #
    vd
    cv
    #
    cmap
    co
    #
    vy
    @34
    @8
    vx
    @36
    crab
    #
    cmpt
    #
    cmpt
    #
    cmpt2
    vd
    vc
    cvv
    cvv
    vg
    @37
    vu
    @34
    @21
    vv
    @36
    crab
    #
    cmpt
    #
    cmpt
    #
    cmpt2
    fsovd.fs
    va
    vb
    vd
    vc
    cvv
    cvv
    @33
    @40
    vf
    @28
    @36
    cmap
    co
    #
    vy
    @27
    @38
    cmpt
    #
    cmpt
    va
    vd
    weq
    #
    vf
    @30
    @32
    @44
    @45
    @29
    @36
    @28
    cmap
    oveq2
    @46
    vy
    @27
    @31
    @38
    @8
    vx
    @29
    @36
    rabeq
    mpteq2dv
    mpteq12dv
    vb
    vc
    weq
    #
    vf
    @44
    @45
    @37
    @39
    @47
    @28
    @35
    @36
    cmap
    @27
    @34
    pweq
    oveq1d
    vy
    @27
    @34
    @38
    mpteq1
    mpteq12dv
    cbvmpt2v
    vd
    vc
    cvv
    cvv
    @40
    cvv
    cvv
    @43
    cvv
    eqid
    #
    @48
    @40
    vg
    @37
    vy
    @34
    @4
    @5
    @19
    cfv
    #
    wcel
    #
    vx
    @36
    crab
    #
    cmpt
    #
    cmpt
    @43
    vf
    vg
    @37
    @39
    @52
    vf
    vg
    weq
    #
    vy
    @34
    @38
    @51
    @53
    @8
    @50
    vx
    @36
    @53
    @7
    @49
    @4
    @5
    @6
    @19
    fveq1
    eleq2d
    rabbidv
    mpteq2dv
    cbvmptv
    vg
    @37
    @52
    @42
    @52
    vu
    @34
    @2
    @49
    wcel
    #
    vx
    @36
    crab
    #
    cmpt
    @42
    vy
    vu
    @34
    @51
    @55
    vy
    vu
    weq
    @50
    @54
    vx
    @36
    @4
    @2
    @49
    eleq1
    rabbidv
    cbvmptv
    vu
    @34
    @55
    @41
    @54
    @21
    vx
    vv
    @36
    vx
    vv
    weq
    @49
    @20
    @2
    @5
    @3
    @19
    fveq2
    eleq2d
    cbvrabv
    mpteq2i
    eqtri
    mpteq2i
    eqtri
    mpt2eq123i
    3eqtri
    fsovd.b
    fsovd.a
    fsovd
    syl5eq
    @19
    @10
    wceq
    #
    vu
    cA
    @22
    @13
    @56
    @21
    @12
    vv
    cB
    @56
    @20
    @11
    @2
    @3
    @19
    @10
    fveq1
    eleq2d
    rabbidv
    mpteq2dv
    fmptco
    wph
    vf
    @1
    @14
    @6
    wph
    @25
    wa
    #
    @14
    vu
    cA
    @2
    @6
    cfv
    #
    cmpt
    #
    @6
    @57
    vu
    cA
    @13
    @58
    @57
    @2
    cA
    wcel
    #
    wa
    #
    @13
    @3
    @58
    wcel
    #
    vv
    cB
    crab
    #
    @58
    wph
    @60
    @13
    @63
    wceq
    @25
    wph
    @60
    wa
    #
    @12
    @62
    vv
    cB
    @64
    @3
    cB
    wcel
    #
    wa
    #
    @12
    @2
    @3
    @7
    wcel
    #
    vx
    cA
    crab
    #
    wcel
    #
    @62
    @66
    @11
    @68
    @2
    @66
    vy
    @3
    @9
    @68
    cB
    @10
    cvv
    @66
    @10
    eqidd
    vy
    vv
    weq
    #
    @9
    @68
    wceq
    @66
    @70
    @8
    @67
    vx
    cA
    @4
    @3
    @7
    eleq1
    rabbidv
    adantl
    @64
    @65
    simpr
    wph
    @68
    cvv
    wcel
    #
    @60
    @65
    wph
    @26
    @71
    fsovd.a
    @67
    vx
    cA
    cV
    rabexg
    syl
    ad2antrr
    fvmptd
    eleq2d
    @60
    @69
    @62
    wb
    wph
    @65
    @67
    @62
    vx
    @2
    cA
    vx
    vu
    weq
    @7
    @58
    @3
    @5
    @2
    @6
    fveq2
    eleq2d
    elrab3
    ad2antlr
    bitrd
    rabbidva
    adantlr
    @61
    @63
    cB
    @58
    cin
    #
    @58
    vv
    cB
    @58
    dfin5
    @61
    @58
    cB
    wss
    @72
    @58
    wceq
    @61
    @58
    cB
    @61
    cA
    @0
    @2
    @6
    @25
    cA
    @0
    @6
    wf
    wph
    @60
    @6
    @0
    cA
    elmapi
    #
    ad2antlr
    @57
    @60
    simpr
    ffvelrnd
    elpwid
    @58
    cB
    sseqin2
    sylib
    syl5reqr
    eqtr4d
    mpteq2dva
    @25
    @6
    @59
    wceq
    wph
    @25
    vu
    cA
    @0
    @6
    @73
    feqmptd
    adantl
    eqtr4d
    mpteq2dva
    @15
    @16
    wceq
    wph
    vf
    @1
    mptresid
    a1i
    3eqtrd
end
