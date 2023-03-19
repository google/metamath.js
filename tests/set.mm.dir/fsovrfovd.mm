include "co.mm"
include "cpw.mm"
include "cmap.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "copab.mm"
include "cmpt.mm"
include "ccom.mm"
include "crab.mm"
include "ccnv.mm"
include "cxp.mm"
include "wbr.mm"
include "cvv.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "adantr.mm"
include "wss.mm"
include "wb.mm"
include "elmapi.mm"
include "ffvelrnda.mm"
include "elpwid.mm"
include "sseld.mm"
include "impancom.mm"
include "pm4.71d.mm"
include "ex.mm"
include "pm5.32rd.mm"
include "ancom.mm"
include "anbi1i.mm"
include "syl6bb.mm"
include "opabbidv.mm"
include "opabssxp.mm"
include "syl6eqss.mm"
include "adantl.mm"
include "sselpwd.mm"
include "eqidd.mm"
include "rfovd.mm"
include "weq.mm"
include "breq.mm"
include "rabbidv.mm"
include "mpteq2dv.mm"
include "breq1.mm"
include "breq2.mm"
include "cbvrabv.mm"
include "syl6eq.mm"
include "cbvmptv.mm"
include "wceq.mm"
include "cop.mm"
include "df-br.mm"
include "vex.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "opelopab.mm"
include "bitri.mm"
include "ibar.mm"
include "bicomd.mm"
include "rabbiia.mm"
include "eqtri.mm"
include "mpteq2i.mm"
include "fmptco.mm"
include "wi.mm"
include "eqid.mm"
include "rfovcnvd.mm"
include "idi.mm"
include "cmpt2.mm"
include "a1i.mm"
include "xpeq12.mm"
include "pweqd.mm"
include "mpteq1d.mm"
include "elexd.mm"
include "pwexg.mm"
include "mptexg.mm"
include "3syl.mm"
include "ovmpt2d.mm"
include "cnveq.mm"
include "cnvopab.mm"
include "coeq2d.mm"
include "fsovd.mm"
include "3eqtr4rd.mm"

theorem fsovrfovd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vf: setvar f
  let cO: class O
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vt: setvar t
  assume fsovd.fs: |- O = ( a e. _V , b e. _V |-> ( f e. ( ~P b ^m a ) |-> ( y e. b |-> { x e. a | y e. ( f ` x ) } ) ) )
  assume fsovd.a: |- ( ph -> A e. V )
  assume fsovd.b: |- ( ph -> B e. W )
  assume fsovd.rf: |- R = ( a e. _V , b e. _V |-> ( r e. ~P ( a X. b ) |-> ( u e. a |-> { v e. b | u r v } ) ) )
  assume fsovd.cnv: |- C = ( a e. _V , b e. _V |-> ( s e. ~P ( a X. b ) |-> `' s ) )

  disjoint A a
  disjoint A b
  disjoint A f
  disjoint A r
  disjoint A u
  disjoint A v
  disjoint a b
  disjoint a f
  disjoint a r
  disjoint a u
  disjoint a v
  disjoint b f
  disjoint b r
  disjoint b u
  disjoint b v
  disjoint f r
  disjoint f u
  disjoint f v
  disjoint r u
  disjoint r v
  disjoint u v
  disjoint A s
  disjoint a s
  disjoint b s
  disjoint f s
  disjoint s u
  disjoint s v
  disjoint A x
  disjoint A y
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint B a
  disjoint B b
  disjoint B f
  disjoint B r
  disjoint B u
  disjoint B v
  disjoint B s
  disjoint B y
  disjoint W a
  disjoint W u
  disjoint a ph
  disjoint b ph
  disjoint f ph
  disjoint ph r
  disjoint ph u
  disjoint ph v
  disjoint A c
  disjoint A d
  disjoint A t
  disjoint c d
  disjoint c f
  disjoint c r
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint d f
  disjoint d r
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint f t
  disjoint r t
  disjoint t u
  disjoint t v
  disjoint c x
  disjoint c y
  disjoint t x
  disjoint t y
  disjoint d x
  disjoint B d
  disjoint a d
  disjoint b d
  disjoint d s
  disjoint B c
  disjoint B t
  assert |- ( ph -> ( A O B ) = ( ( B R A ) o. ( ( A C B ) o. `' ( A R B ) ) ) )

  proof
    wph
    cB
    cA
    cR
    co
    #
    vf
    cB
    cpw
    #
    cA
    cmap
    co
    #
    vu
    cv
    #
    cA
    wcel
    #
    vv
    cv
    #
    @3
    vf
    cv
    #
    cfv
    #
    wcel
    #
    wa
    #
    vv
    vu
    copab
    #
    cmpt
    #
    ccom
    vf
    @2
    vy
    cB
    vy
    cv
    #
    vx
    cv
    #
    @6
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
    cmpt
    @0
    cA
    cB
    cC
    co
    #
    cA
    cB
    cR
    co
    #
    ccnv
    #
    ccom
    #
    ccom
    cA
    cB
    cO
    co
    wph
    vf
    vt
    @2
    cB
    cA
    cxp
    #
    cpw
    #
    @10
    vc
    cB
    vc
    cv
    #
    vd
    cv
    #
    vt
    cv
    #
    wbr
    #
    vd
    cA
    crab
    #
    cmpt
    #
    @17
    @11
    @0
    wph
    @6
    @2
    wcel
    #
    wa
    #
    @10
    @22
    cvv
    wph
    @22
    cvv
    wcel
    #
    @30
    wph
    cB
    cW
    wcel
    #
    cA
    cV
    wcel
    #
    @32
    fsovd.b
    fsovd.a
    cB
    cA
    cW
    cV
    xpexg
    syl2anc
    adantr
    @30
    @10
    @22
    wss
    wph
    @30
    @10
    @5
    cB
    wcel
    #
    @4
    wa
    #
    @8
    wa
    #
    vv
    vu
    copab
    @22
    @30
    @9
    @37
    vv
    vu
    @30
    @9
    @4
    @35
    wa
    #
    @8
    wa
    #
    @37
    @30
    @8
    @4
    @38
    @30
    @8
    @4
    @38
    wb
    @30
    @8
    wa
    @4
    @35
    @30
    @4
    @8
    @35
    @30
    @4
    wa
    #
    @7
    cB
    @5
    @40
    @7
    cB
    @30
    cA
    @1
    @3
    @6
    @6
    @1
    cA
    elmapi
    ffvelrnda
    elpwid
    sseld
    impancom
    pm4.71d
    ex
    pm5.32rd
    #
    @38
    @36
    @8
    @4
    @35
    ancom
    anbi1i
    syl6bb
    opabbidv
    @8
    vv
    vu
    cB
    cA
    opabssxp
    syl6eqss
    adantl
    sselpwd
    wph
    @11
    eqidd
    wph
    @0
    vr
    @23
    vu
    cB
    @3
    @5
    vr
    cv
    #
    wbr
    #
    vv
    cA
    crab
    #
    cmpt
    #
    cmpt
    vt
    @23
    @29
    cmpt
    wph
    vu
    vv
    cB
    cA
    cR
    cW
    cV
    vr
    va
    vb
    fsovd.rf
    fsovd.b
    fsovd.a
    rfovd
    vr
    vt
    @23
    @45
    @29
    vr
    vt
    weq
    #
    @45
    vu
    cB
    @3
    @5
    @26
    wbr
    #
    vv
    cA
    crab
    #
    cmpt
    @29
    @46
    vu
    cB
    @44
    @48
    @46
    @43
    @47
    vv
    cA
    @3
    @5
    @42
    @26
    breq
    rabbidv
    mpteq2dv
    vu
    vc
    cB
    @48
    @28
    vu
    vc
    weq
    #
    @48
    @24
    @5
    @26
    wbr
    #
    vv
    cA
    crab
    @28
    @49
    @47
    @50
    vv
    cA
    @3
    @24
    @5
    @26
    breq1
    rabbidv
    @50
    @27
    vv
    vd
    cA
    @5
    @25
    @24
    @26
    breq2
    cbvrabv
    syl6eq
    cbvmptv
    syl6eq
    cbvmptv
    syl6eq
    @26
    @10
    wceq
    #
    @29
    vc
    cB
    @25
    cA
    wcel
    #
    @24
    @25
    @6
    cfv
    #
    wcel
    #
    wa
    #
    vd
    cA
    crab
    #
    cmpt
    #
    @17
    @51
    vc
    cB
    @28
    @56
    @51
    @27
    @55
    vd
    cA
    @51
    @27
    @24
    @25
    @10
    wbr
    #
    @55
    @24
    @25
    @26
    @10
    breq
    @58
    @24
    @25
    cop
    @10
    wcel
    @55
    @24
    @25
    @10
    df-br
    @9
    @4
    @24
    @7
    wcel
    #
    wa
    @55
    vv
    vu
    @24
    @25
    vc
    vex
    vd
    vex
    vv
    vc
    weq
    @8
    @59
    @4
    @5
    @24
    @7
    eleq1
    anbi2d
    vu
    vd
    weq
    #
    @4
    @52
    @59
    @54
    @3
    @25
    cA
    eleq1
    @60
    @7
    @53
    @24
    @3
    @25
    @6
    fveq2
    eleq2d
    anbi12d
    opelopab
    bitri
    syl6bb
    rabbidv
    mpteq2dv
    @57
    vc
    cB
    @24
    @14
    wcel
    #
    vx
    cA
    crab
    #
    cmpt
    @17
    vc
    cB
    @56
    @62
    @56
    @54
    vd
    cA
    crab
    @62
    @55
    @54
    vd
    cA
    @52
    @54
    @55
    @52
    @54
    ibar
    bicomd
    rabbiia
    @54
    @61
    vd
    vx
    cA
    vd
    vx
    weq
    @53
    @14
    @24
    @25
    @13
    @6
    fveq2
    eleq2d
    cbvrabv
    eqtri
    mpteq2i
    vc
    vy
    cB
    @62
    @16
    vc
    vy
    weq
    @61
    @15
    vx
    cA
    @24
    @12
    @14
    eleq1
    rabbidv
    cbvmptv
    eqtri
    syl6eq
    fmptco
    wph
    @21
    @11
    @0
    wph
    vf
    vs
    @2
    cA
    cB
    cxp
    #
    cpw
    #
    @9
    vu
    vv
    copab
    #
    vs
    cv
    #
    ccnv
    #
    @10
    @20
    @18
    @31
    @65
    @63
    cvv
    wph
    @63
    cvv
    wcel
    #
    @30
    wph
    @34
    @33
    @68
    fsovd.a
    fsovd.b
    cA
    cB
    cV
    cW
    xpexg
    syl2anc
    #
    adantr
    @30
    @65
    @63
    wss
    wph
    @30
    @65
    @39
    vu
    vv
    copab
    @63
    @30
    @9
    @39
    vu
    vv
    @41
    opabbidv
    @8
    vu
    vv
    cA
    cB
    opabssxp
    syl6eqss
    adantl
    sselpwd
    wph
    @20
    vf
    @2
    @65
    cmpt
    wceq
    wi
    wph
    vu
    vv
    cA
    cB
    vf
    @19
    cR
    cV
    cW
    vr
    va
    vb
    fsovd.rf
    fsovd.a
    fsovd.b
    @19
    eqid
    rfovcnvd
    idi
    wph
    va
    vb
    cA
    cB
    cvv
    cvv
    vs
    va
    cv
    #
    vb
    cv
    #
    cxp
    #
    cpw
    #
    @67
    cmpt
    #
    vs
    @64
    @67
    cmpt
    #
    cC
    cvv
    cC
    va
    vb
    cvv
    cvv
    @74
    cmpt2
    wceq
    wph
    fsovd.cnv
    a1i
    @70
    cA
    wceq
    @71
    cB
    wceq
    wa
    #
    @74
    @75
    wceq
    wph
    @76
    vs
    @73
    @64
    @67
    @76
    @72
    @63
    @70
    cA
    @71
    cB
    xpeq12
    pweqd
    mpteq1d
    adantl
    wph
    cA
    cV
    fsovd.a
    elexd
    wph
    cB
    cW
    fsovd.b
    elexd
    wph
    @68
    @64
    cvv
    wcel
    @75
    cvv
    wcel
    @69
    @63
    cvv
    pwexg
    vs
    @64
    @67
    cvv
    mptexg
    3syl
    ovmpt2d
    @66
    @65
    wceq
    @67
    @65
    ccnv
    @10
    @66
    @65
    cnveq
    @9
    vu
    vv
    cnvopab
    syl6eq
    fmptco
    coeq2d
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
    3eqtr4rd
end
