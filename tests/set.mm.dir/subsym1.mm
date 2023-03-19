include "wfal.mm"
include "wsb.mm"
include "weq.mm"
include "wi.mm"
include "wa.mm"
include "wex.mm"
include "fal.mm"
include "intnan.mm"
include "nex.mm"
include "df-sb.mm"
include "mtbir.mm"
include "pm2.21i.mm"

theorem subsym1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ x / y ] [ x / y ] F. -> [ x / y ] ph )

  proof
    wfal
    vy
    vx
    wsb
    #
    vy
    vx
    wsb
    #
    wph
    vy
    vx
    wsb
    @1
    vy
    vx
    weq
    #
    @0
    wi
    #
    @2
    @0
    wa
    #
    vy
    wex
    #
    wa
    @5
    @3
    @4
    vy
    @0
    @2
    @0
    @2
    wfal
    wi
    #
    @2
    wfal
    wa
    #
    vy
    wex
    #
    wa
    @8
    @6
    @7
    vy
    wfal
    @2
    fal
    intnan
    nex
    intnan
    wfal
    vy
    vx
    df-sb
    mtbir
    intnan
    nex
    intnan
    @0
    vy
    vx
    df-sb
    mtbir
    pm2.21i
end
