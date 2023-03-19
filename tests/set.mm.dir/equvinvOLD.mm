include "weq.mm"
include "wa.mm"
include "wex.mm"
include "equviniva.mm"
include "wi.mm"
include "equtrr.mm"
include "equcoms.mm"
include "impcom.mm"
include "exlimiv.mm"
include "impbii.mm"

theorem equvinvOLD
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  disjoint y z
  assert |- ( x = y <-> E. z ( x = z /\ y = z ) )

  proof
    vx
    vy
    weq
    #
    vx
    vz
    weq
    #
    vy
    vz
    weq
    #
    wa
    #
    vz
    wex
    vx
    vy
    vz
    equviniva
    @3
    @0
    vz
    @2
    @1
    @0
    @1
    @0
    wi
    vz
    vy
    vz
    vy
    vx
    equtrr
    equcoms
    impcom
    exlimiv
    impbii
end
