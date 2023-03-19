include "weq.mm"
include "wi.mm"
include "equtrr.mm"
include "equcoms.mm"
include "impcom.mm"

theorem equtr2OLD
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( x = z /\ y = z ) -> x = y )

  proof
    vy
    vz
    weq
    vx
    vz
    weq
    #
    vx
    vy
    weq
    #
    @0
    @1
    wi
    vz
    vy
    vz
    vy
    vx
    equtrr
    equcoms
    impcom
end
