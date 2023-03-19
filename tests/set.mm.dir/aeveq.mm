include "weq.mm"
include "wal.mm"
include "wex.mm"
include "aevlem.mm"
include "ax6ev.mm"
include "ax7.mm"
include "aleximi.mm"
include "mpi.mm"
include "ax5e.mm"
include "3syl.mm"

theorem aeveq
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vu: setvar u

  disjoint x y
  disjoint u z
  disjoint t u
  assert |- ( A. x x = y -> z = t )

  proof
    vx
    vy
    weq
    vx
    wal
    vu
    vz
    weq
    #
    vu
    wal
    #
    vz
    vt
    weq
    #
    vu
    wex
    #
    @2
    vx
    vy
    vu
    vz
    aevlem
    @1
    vu
    vt
    weq
    #
    vu
    wex
    @3
    vu
    vt
    ax6ev
    @0
    @4
    @2
    vu
    vu
    vz
    vt
    ax7
    aleximi
    mpi
    @2
    vu
    ax5e
    3syl
end
