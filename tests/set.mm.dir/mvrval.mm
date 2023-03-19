include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "mvrfval.mm"
include "fveq1d.mm"
include "wcel.mm"
include "eqeq2.mm"
include "ifbid.mm"
include "mpteq2dv.mm"
include "eqeq2d.mm"
include "eqid.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "ovex.mm"
include "rabex2.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eqtrd.mm"

theorem mvrval
  let wph: wff ph
  let vy: setvar y
  let cD: class D
  let cR: class R
  let c.1: class .1.
  let vf: setvar f
  let vh: setvar h
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vi: setvar i
  let vr: setvar r
  let vx: setvar x
  let cF: class F
  assume mvrfval.v: |- V = ( I mVar R )
  assume mvrfval.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume mvrfval.z: |- .0. = ( 0g ` R )
  assume mvrfval.o: |- .1. = ( 1r ` R )
  assume mvrfval.i: |- ( ph -> I e. W )
  assume mvrfval.r: |- ( ph -> R e. Y )
  assume mvrval.x: |- ( ph -> X e. I )

  disjoint .0. f
  disjoint .1. f
  disjoint f y
  disjoint D f
  disjoint D y
  disjoint W y
  disjoint f h
  disjoint I f
  disjoint h y
  disjoint I h
  disjoint I y
  disjoint R f
  disjoint X f
  disjoint X h
  disjoint X y
  disjoint f i
  disjoint f r
  disjoint f x
  disjoint i r
  disjoint i x
  disjoint .0. i
  disjoint r x
  disjoint .0. r
  disjoint .0. x
  disjoint .1. i
  disjoint .1. r
  disjoint .1. x
  disjoint i y
  disjoint D i
  disjoint r y
  disjoint D r
  disjoint x y
  disjoint D x
  disjoint F f
  disjoint h i
  disjoint h r
  disjoint h x
  disjoint I i
  disjoint I r
  disjoint I x
  disjoint R i
  disjoint R r
  disjoint R x
  disjoint X x
  assert |- ( ph -> ( V ` X ) = ( f e. D |-> if ( f = ( y e. I |-> if ( y = X , 1 , 0 ) ) , .1. , .0. ) ) )

  proof
    wph
    cX
    cV
    cfv
    cX
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
    #
    vx
    cv
    #
    wceq
    #
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
    cfv
    #
    vf
    cD
    @0
    vy
    cI
    @1
    cX
    wceq
    #
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
    wph
    cX
    cV
    @9
    wph
    vx
    vy
    cD
    cR
    c.1
    vf
    vh
    cI
    cV
    cW
    cY
    c.0
    mvrfval.v
    mvrfval.d
    mvrfval.z
    mvrfval.o
    mvrfval.i
    mvrfval.r
    mvrfval
    fveq1d
    wph
    cX
    cI
    wcel
    @10
    @16
    wceq
    mvrval.x
    vx
    cX
    @8
    @16
    cI
    @9
    @2
    cX
    wceq
    #
    vf
    cD
    @7
    @15
    @17
    @6
    @14
    c.1
    c.0
    @17
    @5
    @13
    @0
    @17
    vy
    cI
    @4
    @12
    @17
    @3
    @11
    c1
    cc0
    @2
    cX
    @1
    eqeq2
    ifbid
    mpteq2dv
    eqeq2d
    ifbid
    mpteq2dv
    @9
    eqid
    vf
    cD
    @15
    vh
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vh
    cn0
    cI
    cmap
    co
    cD
    mvrfval.d
    cn0
    cI
    cmap
    ovex
    rabex2
    mptex
    fvmpt
    syl
    eqtrd
end
