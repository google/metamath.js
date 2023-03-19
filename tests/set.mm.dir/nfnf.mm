include "wnf.mm"
include "wex.mm"
include "wal.mm"
include "wi.mm"
include "df-nf.mm"
include "nfex.mm"
include "nfal.mm"
include "nfim.mm"
include "nfxfr.mm"

theorem nfnf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume nfnf.1: |- F/ x ph


  assert |- F/ x F/ y ph

  proof
    wph
    vy
    wnf
    wph
    vy
    wex
    #
    wph
    vy
    wal
    #
    wi
    vx
    wph
    vy
    df-nf
    @0
    @1
    vx
    wph
    vx
    vy
    nfnf.1
    nfex
    wph
    vx
    vy
    nfnf.1
    nfal
    nfim
    nfxfr
end
