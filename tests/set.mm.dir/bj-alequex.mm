include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "ax6e.mm"
include "exim.mm"
include "mpi.mm"

theorem bj-alequex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ( x = y -> ph ) -> E. x ph )

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
    wph
    vx
    wex
    vx
    vy
    ax6e
    @0
    wph
    vx
    exim
    mpi
end
