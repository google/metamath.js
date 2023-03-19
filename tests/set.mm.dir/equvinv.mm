include "weq.mm"
include "wa.mm"
include "wex.mm"
include "ax6ev.mm"
include "equtrr.mm"
include "ancld.mm"
include "eximdv.mm"
include "mpi.mm"
include "ax7.mm"
include "imp.mm"
include "exlimiv.mm"
include "impbii.mm"

theorem equvinv
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z

  disjoint x z
  disjoint y z
  assert |- ( x = y <-> E. z ( z = x /\ z = y ) )

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
    vy
    weq
    #
    wa
    #
    vz
    wex
    #
    @0
    @1
    vz
    wex
    @4
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
    @3
    @0
    vz
    @1
    @2
    @0
    vz
    vx
    vy
    ax7
    imp
    exlimiv
    impbii
end
