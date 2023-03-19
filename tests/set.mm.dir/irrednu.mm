include "wcel.mm"
include "cbs.mm"
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
include "simp2bi.mm"

theorem irrednu
  let cR: class R
  let cU: class U
  let cI: class I
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.x: class .x.
  let cY: class Y
  let cB: class B
  let c.0: class .0.
  assume irredn0.i: |- I = ( Irred ` R )
  assume irrednu.u: |- U = ( Unit ` R )


  assert |- ( X e. I -> -. X e. U )

  proof
    cX
    cI
    wcel
    cX
    cR
    cbs
    cfv
    #
    wcel
    cX
    cU
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
    cU
    wcel
    @2
    cU
    wcel
    wo
    wi
    vy
    @0
    wral
    vx
    @0
    wral
    vx
    vy
    @0
    cR
    @3
    cU
    cI
    cX
    @0
    eqid
    irrednu.u
    irredn0.i
    @3
    eqid
    isirred2
    simp2bi
end
