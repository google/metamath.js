include "cv.mm"
include "wceq.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "1nn0.mm"
include "snifpsrbag.mm"
include "sylancl.mm"
include "mvrval2.mm"
include "eqid.mm"
include "iftruei.mm"
include "syl6eq.mm"

theorem mvrid
  let wph: wff ph
  let vy: setvar y
  let cD: class D
  let cR: class R
  let c.1: class .1.
  let vh: setvar h
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vf: setvar f
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

  disjoint D y
  disjoint W y
  disjoint h y
  disjoint I h
  disjoint I y
  disjoint X h
  disjoint X y
  disjoint f i
  disjoint f r
  disjoint f x
  disjoint .0. f
  disjoint i r
  disjoint i x
  disjoint .0. i
  disjoint r x
  disjoint .0. r
  disjoint .0. x
  disjoint .1. f
  disjoint .1. i
  disjoint .1. r
  disjoint .1. x
  disjoint f y
  disjoint D f
  disjoint i y
  disjoint D i
  disjoint r y
  disjoint D r
  disjoint x y
  disjoint D x
  disjoint F f
  disjoint f h
  disjoint I f
  disjoint h i
  disjoint h r
  disjoint h x
  disjoint I i
  disjoint I r
  disjoint I x
  disjoint R f
  disjoint R i
  disjoint R r
  disjoint R x
  disjoint X f
  disjoint X x
  assert |- ( ph -> ( ( V ` X ) ` ( y e. I |-> if ( y = X , 1 , 0 ) ) ) = .1. )

  proof
    wph
    vy
    cI
    vy
    cv
    cX
    wceq
    c1
    cc0
    cif
    cmpt
    #
    cX
    cV
    cfv
    cfv
    @0
    @0
    wceq
    #
    c.1
    c.0
    cif
    c.1
    wph
    vy
    cD
    cR
    c.1
    vh
    @0
    cI
    cV
    cW
    cX
    cY
    c.0
    mvrfval.v
    mvrfval.d
    mvrfval.z
    mvrfval.o
    mvrfval.i
    mvrfval.r
    mvrval.x
    wph
    cI
    cW
    wcel
    c1
    cn0
    wcel
    @0
    cD
    wcel
    mvrfval.i
    1nn0
    vy
    cD
    vh
    cI
    c1
    cW
    cX
    mvrfval.d
    snifpsrbag
    sylancl
    mvrval2
    @1
    c.1
    c.0
    @0
    eqid
    iftruei
    syl6eq
end
