include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "ax6ev.mm"
include "exim.mm"
include "mpi.mm"

theorem bj-alequexv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
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
    ax6ev
    @0
    wph
    vx
    exim
    mpi
end
