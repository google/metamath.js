include "ccla.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "simpl.mm"
include "clatlubcl2.mm"
include "lubprop.mm"

theorem lublem
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cS: class S
  let cU: class U
  let cK: class K
  let c.le: class .<_
  assume lublem.b: |- B = ( Base ` K )
  assume lublem.l: |- .<_ = ( le ` K )
  assume lublem.u: |- U = ( lub ` K )

  disjoint B z
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint S y
  disjoint S z
  disjoint U y
  disjoint U z
  disjoint .<_ y
  disjoint .<_ z
  assert |- ( ( K e. CLat /\ S C_ B ) -> ( A. y e. S y .<_ ( U ` S ) /\ A. z e. B ( A. y e. S y .<_ z -> ( U ` S ) .<_ z ) ) )

  proof
    cK
    ccla
    wcel
    #
    cS
    cB
    wss
    #
    wa
    vy
    vz
    cB
    cS
    cU
    cK
    c.le
    ccla
    lublem.b
    lublem.l
    lublem.u
    @0
    @1
    simpl
    cB
    cS
    cU
    cK
    lublem.b
    lublem.u
    clatlubcl2
    lubprop
end
