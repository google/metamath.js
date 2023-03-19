include "cgrp.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "cga.mm"
include "cghm.mm"
include "eqid.mm"
include "gaid2.mm"
include "cmpt.mm"
include "oveq12.mm"
include "ovex.mm"
include "ovmpt2a.mm"
include "mpteq2dva.mm"
include "mpteq2ia.mm"
include "eqtr4i.mm"
include "galactghm.mm"
include "syl.mm"

theorem cayleylem1
  let c.pl: class .+
  let cS: class S
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let c.0: class .0.
  let va: setvar a
  let vx: setvar x
  let vy: setvar y
  assume cayleylem1.x: |- X = ( Base ` G )
  assume cayleylem1.p: |- .+ = ( +g ` G )
  assume cayleylem1.u: |- .0. = ( 0g ` G )
  assume cayleylem1.h: |- H = ( SymGrp ` X )
  assume cayleylem1.s: |- S = ( Base ` H )
  assume cayleylem1.f: |- F = ( g e. X |-> ( a e. X |-> ( g .+ a ) ) )

  disjoint a g
  disjoint .+ a
  disjoint .+ g
  disjoint G a
  disjoint G g
  disjoint H g
  disjoint X a
  disjoint X g
  disjoint .0. a
  disjoint a x
  disjoint a y
  disjoint g x
  disjoint g y
  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint F x
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint X x
  disjoint X y
  disjoint .0. x
  disjoint S x
  assert |- ( G e. Grp -> F e. ( G GrpHom H ) )

  proof
    cG
    cgrp
    wcel
    vx
    vy
    cX
    cX
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    cmpt2
    #
    cG
    cX
    cga
    co
    wcel
    cF
    cG
    cH
    cghm
    co
    wcel
    vx
    vy
    c.pl
    @3
    cG
    cX
    cayleylem1.x
    cayleylem1.p
    @3
    eqid
    #
    gaid2
    vg
    va
    @3
    cF
    cG
    cH
    cX
    cX
    cayleylem1.x
    cayleylem1.h
    cF
    vg
    cX
    va
    cX
    vg
    cv
    #
    va
    cv
    #
    c.pl
    co
    #
    cmpt
    #
    cmpt
    vg
    cX
    va
    cX
    @5
    @6
    @3
    co
    #
    cmpt
    #
    cmpt
    cayleylem1.f
    vg
    cX
    @10
    @8
    @5
    cX
    wcel
    va
    cX
    @9
    @7
    vx
    vy
    @5
    @6
    cX
    cX
    @2
    @7
    @3
    @0
    @5
    @1
    @6
    c.pl
    oveq12
    @4
    @5
    @6
    c.pl
    ovex
    ovmpt2a
    mpteq2dva
    mpteq2ia
    eqtr4i
    galactghm
    syl
end
