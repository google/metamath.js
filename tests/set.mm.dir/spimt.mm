include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wnf.mm"
include "ax6e.mm"
include "exim.mm"
include "mpi.mm"
include "19.35.mm"
include "sylib.mm"
include "19.9t.mm"
include "biimpd.mm"
include "sylan9r.mm"

theorem spimt
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F/ x ps /\ A. x ( x = y -> ( ph -> ps ) ) ) -> ( A. x ph -> ps ) )

  proof
    vx
    vy
    weq
    #
    wph
    wps
    wi
    #
    wi
    vx
    wal
    #
    wph
    vx
    wal
    #
    wps
    vx
    wex
    #
    wps
    vx
    wnf
    #
    wps
    @2
    @1
    vx
    wex
    #
    @3
    @4
    wi
    @2
    @0
    vx
    wex
    @6
    vx
    vy
    ax6e
    @0
    @1
    vx
    exim
    mpi
    wph
    wps
    vx
    19.35
    sylib
    @5
    @4
    wps
    wps
    vx
    19.9t
    biimpd
    sylan9r
end
