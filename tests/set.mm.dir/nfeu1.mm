include "weu.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "df-eu.mm"
include "nfa1.mm"
include "nfex.mm"
include "nfxfr.mm"

theorem nfeu1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- F/ x E! x ph

  proof
    wph
    vx
    weu
    wph
    vx
    vy
    weq
    wb
    #
    vx
    wal
    #
    vy
    wex
    vx
    wph
    vx
    vy
    df-eu
    @1
    vx
    vy
    @0
    vx
    nfa1
    nfex
    nfxfr
end
