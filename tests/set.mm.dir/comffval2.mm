include "cop.mm"
include "co.mm"
include "chom.mm"
include "cfv.mm"
include "cv.mm"
include "cmpt2.mm"
include "eqid.mm"
include "comffval.mm"
include "homfval.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "eqtr4d.mm"

theorem comffval2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume comfffval2.o: |- O = ( comf ` C )
  assume comfffval2.b: |- B = ( Base ` C )
  assume comfffval2.h: |- H = ( Homf ` C )
  assume comfffval2.x: |- .x. = ( comp ` C )
  assume comffval2.x: |- ( ph -> X e. B )
  assume comffval2.y: |- ( ph -> Y e. B )
  assume comffval2.z: |- ( ph -> Z e. B )

  disjoint f g
  disjoint B f
  disjoint B g
  disjoint C f
  disjoint C g
  disjoint .x. f
  disjoint .x. g
  disjoint X f
  disjoint X g
  disjoint Y f
  disjoint Y g
  disjoint f ph
  disjoint g ph
  disjoint Z f
  disjoint Z g
  disjoint f x
  disjoint f y
  disjoint g x
  disjoint g y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint .x. x
  assert |- ( ph -> ( <. X , Y >. O Z ) = ( g e. ( Y H Z ) , f e. ( X H Y ) |-> ( g ( <. X , Y >. .x. Z ) f ) ) )

  proof
    wph
    cX
    cY
    cop
    #
    cZ
    cO
    co
    vg
    vf
    cY
    cZ
    cC
    chom
    cfv
    #
    co
    #
    cX
    cY
    @1
    co
    #
    vg
    cv
    vf
    cv
    @0
    cZ
    c.x
    co
    co
    #
    cmpt2
    vg
    vf
    cY
    cZ
    cH
    co
    #
    cX
    cY
    cH
    co
    #
    @4
    cmpt2
    wph
    cB
    cC
    c.x
    vf
    vg
    @1
    cO
    cX
    cY
    cZ
    comfffval2.o
    comfffval2.b
    @1
    eqid
    #
    comfffval2.x
    comffval2.x
    comffval2.y
    comffval2.z
    comffval
    wph
    vg
    vf
    @5
    @6
    @4
    @2
    @3
    @4
    wph
    cB
    cC
    cH
    @1
    cY
    cZ
    comfffval2.h
    comfffval2.b
    @7
    comffval2.y
    comffval2.z
    homfval
    wph
    cB
    cC
    cH
    @1
    cX
    cY
    comfffval2.h
    comfffval2.b
    @7
    comffval2.x
    comffval2.y
    homfval
    wph
    @4
    eqidd
    mpt2eq123dv
    eqtr4d
end
