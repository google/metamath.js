include "weq.mm"
include "wi.mm"
include "wal.mm"
include "a2i.mm"
include "alimi.mm"
include "bj-equsal1ti.mm"
include "sylib.mm"

theorem bj-equsal1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-equsal1.1: |- F/ x ps
  assume bj-equsal1.2: |- ( x = y -> ( ph -> ps ) )


  assert |- ( A. x ( x = y -> ph ) -> ps )

  proof
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
    wps
    @1
    @2
    vx
    @0
    wph
    wps
    bj-equsal1.2
    a2i
    alimi
    wps
    vx
    vy
    bj-equsal1.1
    bj-equsal1ti
    sylib
end
