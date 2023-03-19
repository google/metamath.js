include "weq.mm"
include "wal.mm"
include "wi.mm"
include "wex.mm"
include "ax6e.mm"
include "exim.mm"
include "mpi.mm"
include "axc7e.mm"
include "syl.mm"

theorem bj-axc10
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ( x = y -> A. x ph ) -> ph )

  proof
    vx
    vy
    weq
    #
    wph
    vx
    wal
    #
    wi
    vx
    wal
    #
    @1
    vx
    wex
    #
    wph
    @2
    @0
    vx
    wex
    @3
    vx
    vy
    ax6e
    @0
    @1
    vx
    exim
    mpi
    wph
    vx
    axc7e
    syl
end
