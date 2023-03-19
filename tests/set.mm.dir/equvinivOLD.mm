include "weq.mm"
include "wex.mm"
include "wa.mm"
include "ax6ev.mm"
include "equtrr.mm"
include "ancld.mm"
include "eximdv.mm"
include "mpi.mm"

theorem equvinivOLD
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  disjoint y z
  assert |- ( x = y -> E. z ( z = x /\ z = y ) )

  proof
    vx
    vy
    weq
    #
    vz
    vx
    weq
    #
    vz
    wex
    @1
    vz
    vy
    weq
    #
    wa
    #
    vz
    wex
    vz
    vx
    ax6ev
    @0
    @1
    @3
    vz
    @0
    @1
    @2
    vx
    vy
    vz
    equtrr
    ancld
    eximdv
    mpi
end
