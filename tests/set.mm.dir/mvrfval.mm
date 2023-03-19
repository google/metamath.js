include "cmvr.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "elex.mm"
include "syl.mm"
include "mptexg.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "cur.mm"
include "cfv.mm"
include "c0g.mm"
include "wa.mm"
include "simpl.mm"
include "oveq2d.mm"
include "rabeq.mm"
include "syl6eqr.mm"
include "mpteq1.mm"
include "adantr.mm"
include "eqeq2d.mm"
include "simpr.mm"
include "fveq2d.mm"
include "ifbieq12d.mm"
include "mpteq12dv.mm"
include "df-mvr.mm"
include "ovmpt2ga.mm"
include "syl3anc.mm"
include "syl5eq.mm"

theorem mvrfval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cR: class R
  let c.1: class .1.
  let vf: setvar f
  let vh: setvar h
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  let vi: setvar i
  let vr: setvar r
  let cF: class F
  let cX: class X
  assume mvrfval.v: |- V = ( I mVar R )
  assume mvrfval.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume mvrfval.z: |- .0. = ( 0g ` R )
  assume mvrfval.o: |- .1. = ( 1r ` R )
  assume mvrfval.i: |- ( ph -> I e. W )
  assume mvrfval.r: |- ( ph -> R e. Y )

  disjoint f x
  disjoint .0. f
  disjoint .0. x
  disjoint .1. f
  disjoint .1. x
  disjoint f y
  disjoint D f
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint W y
  disjoint f h
  disjoint I f
  disjoint h x
  disjoint h y
  disjoint I h
  disjoint I x
  disjoint I y
  disjoint R f
  disjoint R x
  disjoint f i
  disjoint f r
  disjoint i r
  disjoint i x
  disjoint .0. i
  disjoint r x
  disjoint .0. r
  disjoint .1. i
  disjoint .1. r
  disjoint i y
  disjoint D i
  disjoint r y
  disjoint D r
  disjoint F f
  disjoint h i
  disjoint h r
  disjoint I i
  disjoint I r
  disjoint R i
  disjoint R r
  disjoint X f
  disjoint X h
  disjoint X x
  disjoint X y
  assert |- ( ph -> V = ( x e. I |-> ( f e. D |-> if ( f = ( y e. I |-> if ( y = x , 1 , 0 ) ) , .1. , .0. ) ) ) )

  proof
    wph
    cV
    cI
    cR
    cmvr
    co
    #
    vx
    cI
    vf
    cD
    vf
    cv
    #
    vy
    cI
    vy
    cv
    vx
    cv
    wceq
    c1
    cc0
    cif
    #
    cmpt
    #
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    cmpt
    #
    mvrfval.v
    wph
    cI
    cvv
    wcel
    #
    cR
    cvv
    wcel
    #
    @7
    cvv
    wcel
    #
    @0
    @7
    wceq
    wph
    cI
    cW
    wcel
    #
    @8
    mvrfval.i
    cI
    cW
    elex
    syl
    wph
    cR
    cY
    wcel
    @9
    mvrfval.r
    cR
    cY
    elex
    syl
    wph
    @11
    @10
    mvrfval.i
    vx
    cI
    @6
    cW
    mptexg
    syl
    vi
    vr
    cI
    cR
    cvv
    cvv
    vx
    vi
    cv
    #
    vf
    vh
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    #
    vh
    cn0
    @12
    cmap
    co
    #
    crab
    #
    @1
    vy
    @12
    @2
    cmpt
    #
    wceq
    #
    vr
    cv
    #
    cur
    cfv
    #
    @18
    c0g
    cfv
    #
    cif
    #
    cmpt
    #
    cmpt
    @7
    cmvr
    cvv
    @12
    cI
    wceq
    #
    @18
    cR
    wceq
    #
    wa
    #
    vx
    @12
    @22
    cI
    @6
    @23
    @24
    simpl
    #
    @25
    vf
    @15
    @21
    cD
    @5
    @25
    @15
    @13
    vh
    cn0
    cI
    cmap
    co
    #
    crab
    #
    cD
    @25
    @14
    @27
    wceq
    @15
    @28
    wceq
    @25
    @12
    cI
    cn0
    cmap
    @26
    oveq2d
    @13
    vh
    @14
    @27
    rabeq
    syl
    mvrfval.d
    syl6eqr
    @25
    @17
    @4
    @19
    @20
    c.1
    c.0
    @25
    @16
    @3
    @1
    @23
    @16
    @3
    wceq
    @24
    vy
    @12
    cI
    @2
    mpteq1
    adantr
    eqeq2d
    @25
    @19
    cR
    cur
    cfv
    c.1
    @25
    @18
    cR
    cur
    @23
    @24
    simpr
    #
    fveq2d
    mvrfval.o
    syl6eqr
    @25
    @20
    cR
    c0g
    cfv
    c.0
    @25
    @18
    cR
    c0g
    @29
    fveq2d
    mvrfval.z
    syl6eqr
    ifbieq12d
    mpteq12dv
    mpteq12dv
    vx
    vy
    vf
    vh
    vi
    vr
    df-mvr
    ovmpt2ga
    syl3anc
    syl5eq
end
