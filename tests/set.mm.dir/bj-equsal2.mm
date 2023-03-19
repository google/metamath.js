include "weq.mm"
include "wi.mm"
include "wal.mm"
include "bj-equsal1ti.mm"
include "a2i.mm"
include "alimi.mm"
include "sylbir.mm"

theorem bj-equsal2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-equsal2.1: |- F/ x ph
  assume bj-equsal2.2: |- ( x = y -> ( ph -> ps ) )


  assert |- ( ph -> A. x ( x = y -> ps ) )

  proof
    wph
    vx
    vy
    weq
    #
    wph
    wi
    #
    vx
    wal
    @0
    wps
    wi
    #
    vx
    wal
    wph
    vx
    vy
    bj-equsal2.1
    bj-equsal1ti
    @1
    @2
    vx
    @0
    wph
    wps
    bj-equsal2.2
    a2i
    alimi
    sylbir
end
