include "weq.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "ax12v.mm"
include "ax6ev.mm"
include "exim.mm"
include "syl6mpi.mm"
include "ax6evr.mm"
include "exlimiiv.mm"

theorem 19.8a
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( ph -> E. x ph )

  proof
    vx
    vy
    weq
    #
    wph
    wph
    vx
    wex
    #
    wi
    vy
    @0
    wph
    @0
    wph
    wi
    vx
    wal
    @0
    vx
    wex
    @1
    wph
    vx
    vy
    ax12v
    vx
    vy
    ax6ev
    @0
    wph
    vx
    exim
    syl6mpi
    vy
    vx
    ax6evr
    exlimiiv
end
