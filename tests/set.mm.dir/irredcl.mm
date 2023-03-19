include "wcel.mm"
include "cui.mm"
include "cfv.mm"
include "wn.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "eqid.mm"
include "isirred2.mm"
include "simp1bi.mm"

theorem irredcl
  let cB: class B
  let cR: class R
  let cI: class I
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.x: class .x.
  let cU: class U
  let cY: class Y
  let c.0: class .0.
  assume irredn0.i: |- I = ( Irred ` R )
  assume irredcl.b: |- B = ( Base ` R )


  assert |- ( X e. I -> X e. B )

  proof
    cX
    cI
    wcel
    cX
    cB
    wcel
    cX
    cR
    cui
    cfv
    #
    wcel
    wn
    vx
    cv
    #
    vy
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    cX
    wceq
    @1
    @0
    wcel
    @2
    @0
    wcel
    wo
    wi
    vy
    cB
    wral
    vx
    cB
    wral
    vx
    vy
    cB
    cR
    @3
    @0
    cI
    cX
    irredcl.b
    @0
    eqid
    irredn0.i
    @3
    eqid
    isirred2
    simp1bi
end
