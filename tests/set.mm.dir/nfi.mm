include "wnf.mm"
include "wex.mm"
include "wal.mm"
include "wi.mm"
include "df-nf.mm"
include "mpbir.mm"

theorem nfi
  let wph: wff ph
  let vx: setvar x
  assume nfi.1: |- ( E. x ph -> A. x ph )


  assert |- F/ x ph

  proof
    wph
    vx
    wnf
    wph
    vx
    wex
    wph
    vx
    wal
    wi
    nfi.1
    wph
    vx
    df-nf
    mpbir
end
