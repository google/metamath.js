include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wa.mm"
include "ax6e.mm"
include "exintr.mm"
include "mpi.mm"

theorem equs4
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y


  assert |- ( A. x ( x = y -> ph ) -> E. x ( x = y /\ ph ) )

  proof
    vx
    vy
    weq
    #
    wph
    wi
    vx
    wal
    @0
    vx
    wex
    @0
    wph
    wa
    vx
    wex
    vx
    vy
    ax6e
    @0
    wph
    vx
    exintr
    mpi
end
