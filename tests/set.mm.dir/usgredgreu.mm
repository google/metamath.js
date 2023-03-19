include "cusgr.mm"
include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "usgredg4.mm"
include "eqtr2.mm"
include "vex.mm"
include "preqr2.mm"
include "syl.mm"
include "a1i.mm"
include "ralrimivva.mm"
include "preq2.mm"
include "eqeq2d.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem usgredgreu
  let vy: setvar y
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vz: setvar z
  assume usgredg3.v: |- V = ( Vtx ` G )
  assume usgredg3.e: |- E = ( iEdg ` G )

  disjoint E y
  disjoint G y
  disjoint V y
  disjoint X y
  disjoint Y y
  disjoint E x
  disjoint x y
  disjoint G x
  disjoint V x
  disjoint X x
  disjoint E z
  disjoint x z
  disjoint G z
  disjoint V z
  disjoint X z
  disjoint Y x
  disjoint Y z
  disjoint y z
  assert |- ( ( G e. USGraph /\ X e. dom E /\ Y e. ( E ` X ) ) -> E! y e. V ( E ` X ) = { Y , y } )

  proof
    cG
    cusgr
    wcel
    cX
    cE
    cdm
    wcel
    cY
    cX
    cE
    cfv
    #
    wcel
    w3a
    #
    @0
    cY
    vy
    cv
    #
    cpr
    #
    wceq
    #
    vy
    cV
    wrex
    @4
    @0
    cY
    vx
    cv
    #
    cpr
    #
    wceq
    #
    wa
    #
    vy
    vx
    weq
    #
    wi
    #
    vx
    cV
    wral
    vy
    cV
    wral
    @4
    vy
    cV
    wreu
    vy
    cE
    cG
    cV
    cX
    cY
    usgredg3.v
    usgredg3.e
    usgredg4
    @1
    @10
    vy
    vx
    cV
    cV
    @10
    @1
    @2
    cV
    wcel
    @5
    cV
    wcel
    wa
    wa
    @8
    @3
    @6
    wceq
    @9
    @0
    @3
    @6
    eqtr2
    @2
    @5
    cY
    vy
    vex
    vx
    vex
    preqr2
    syl
    a1i
    ralrimivva
    @4
    @7
    vy
    vx
    cV
    @9
    @3
    @6
    @0
    @2
    @5
    cY
    preq2
    eqeq2d
    reu4
    sylanbrc
end
