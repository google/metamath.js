include "weq.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "alinexa.mm"
include "con2bii.mm"

theorem equs3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E. x ( x = y /\ ph ) <-> -. A. x ( x = y -> -. ph ) )

  proof
    vx
    vy
    weq
    #
    wph
    wn
    wi
    vx
    wal
    @0
    wph
    wa
    vx
    wex
    @0
    wph
    vx
    alinexa
    con2bii
end
