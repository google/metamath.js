include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "mvrval.mm"
include "fveq1d.mm"
include "wcel.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "eqid.mm"
include "cur.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "c0g.mm"
include "ifex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eqtrd.mm"

theorem mvrval2
  let wph: wff ph
  let vy: setvar y
  let cD: class D
  let cR: class R
  let c.1: class .1.
  let vh: setvar h
  let cF: class F
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
  assume mvrfval.v: |- V = ( I mVar R )
  assume mvrfval.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume mvrfval.z: |- .0. = ( 0g ` R )
  assume mvrfval.o: |- .1. = ( 1r ` R )
  assume mvrfval.i: |- ( ph -> I e. W )
  assume mvrfval.r: |- ( ph -> R e. Y )
  assume mvrval.x: |- ( ph -> X e. I )
  assume mvrval2.f: |- ( ph -> F e. D )

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
  assert |- ( ph -> ( ( V ` X ) ` F ) = if ( F = ( y e. I |-> if ( y = X , 1 , 0 ) ) , .1. , .0. ) )

  proof
    wph
    cF
    cX
    cV
    cfv
    #
    cfv
    cF
    vf
    cD
    vf
    cv
    #
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
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    cfv
    #
    cF
    @2
    wceq
    #
    c.1
    c.0
    cif
    #
    wph
    cF
    @0
    @5
    wph
    vy
    cD
    cR
    c.1
    vf
    vh
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
    mvrval
    fveq1d
    wph
    cF
    cD
    wcel
    @6
    @8
    wceq
    mvrval2.f
    vf
    cF
    @4
    @8
    cD
    @5
    @1
    cF
    wceq
    @3
    @7
    c.1
    c.0
    @1
    cF
    @2
    eqeq1
    ifbid
    @5
    eqid
    @7
    c.1
    c.0
    c.1
    cR
    cur
    cfv
    cvv
    mvrfval.o
    cR
    cur
    fvex
    eqeltri
    c.0
    cR
    c0g
    cfv
    cvv
    mvrfval.z
    cR
    c0g
    fvex
    eqeltri
    ifex
    fvmpt
    syl
    eqtrd
end
