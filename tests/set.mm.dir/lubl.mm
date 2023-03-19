include "ccla.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "cfv.mm"
include "wi.mm"
include "wa.mm"
include "lublem.mm"
include "simprd.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "imbi12d.mm"
include "rspccva.mm"
include "stoic3.mm"

theorem lubl
  let vy: setvar y
  let cB: class B
  let cS: class S
  let cU: class U
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vz: setvar z
  assume lublem.b: |- B = ( Base ` K )
  assume lublem.l: |- .<_ = ( le ` K )
  assume lublem.u: |- U = ( lub ` K )

  disjoint K y
  disjoint S y
  disjoint U y
  disjoint .<_ y
  disjoint X y
  disjoint B z
  disjoint y z
  disjoint K z
  disjoint S z
  disjoint U z
  disjoint .<_ z
  disjoint X z
  assert |- ( ( K e. CLat /\ S C_ B /\ X e. B ) -> ( A. y e. S y .<_ X -> ( U ` S ) .<_ X ) )

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
    vz
    cv
    #
    c.le
    wbr
    #
    vy
    cS
    wral
    #
    cS
    cU
    cfv
    #
    @3
    c.le
    wbr
    #
    wi
    #
    vz
    cB
    wral
    #
    cX
    cB
    wcel
    @2
    cX
    c.le
    wbr
    #
    vy
    cS
    wral
    #
    @6
    cX
    c.le
    wbr
    #
    wi
    #
    @0
    @1
    wa
    @2
    @6
    c.le
    wbr
    vy
    cS
    wral
    @9
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
    simprd
    @8
    @13
    vz
    cX
    cB
    @3
    cX
    wceq
    #
    @5
    @11
    @7
    @12
    @14
    @4
    @10
    vy
    cS
    @3
    cX
    @2
    c.le
    breq2
    ralbidv
    @3
    cX
    @6
    c.le
    breq2
    imbi12d
    rspccva
    stoic3
end
