include "wex.mm"
include "wn.mm"
include "wal.mm"
include "df-ex.mm"
include "nfn.mm"
include "nfal.mm"
include "nfxfr.mm"

theorem nfex
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y
  assume nfex.1: |- F/ x ph


  assert |- F/ x E. y ph

  proof
    wph
    vy
    wex
    wph
    wn
    #
    vy
    wal
    #
    wn
    vx
    wph
    vy
    df-ex
    @1
    vx
    @0
    vx
    vy
    wph
    vx
    nfex.1
    nfn
    nfal
    nfn
    nfxfr
end
