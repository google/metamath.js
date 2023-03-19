include "ccla.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "cfv.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "wi.mm"
include "lublem.mm"
include "simpld.mm"
include "breq1.mm"
include "rspccva.mm"
include "stoic3.mm"

theorem lubub
  let cB: class B
  let cS: class S
  let cU: class U
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vz: setvar z
  let vy: setvar y
  assume lublem.b: |- B = ( Base ` K )
  assume lublem.l: |- .<_ = ( le ` K )
  assume lublem.u: |- U = ( lub ` K )


  assert |- ( ( K e. CLat /\ S C_ B /\ X e. S ) -> X .<_ ( U ` S ) )

  proof
    cK
    ccla
    wcel
    #
    cS
    cB
    wss
    #
    vy
    cv
    #
    cS
    cU
    cfv
    #
    c.le
    wbr
    #
    vy
    cS
    wral
    #
    cX
    cS
    wcel
    cX
    @3
    c.le
    wbr
    #
    @0
    @1
    wa
    @5
    @2
    vz
    cv
    #
    c.le
    wbr
    vy
    cS
    wral
    @3
    @7
    c.le
    wbr
    wi
    vz
    cB
    wral
    vy
    vz
    cB
    cS
    cU
    cK
    c.le
    lublem.b
    lublem.l
    lublem.u
    lublem
    simpld
    @4
    @6
    vy
    cX
    cS
    @2
    cX
    @3
    c.le
    breq1
    rspccva
    stoic3
end
