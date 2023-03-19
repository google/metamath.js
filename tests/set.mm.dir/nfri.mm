include "wnf.mm"
include "wex.mm"
include "wal.mm"
include "wi.mm"
include "df-nf.mm"
include "mpbi.mm"

theorem nfri
  let wph: wff ph
  let vx: setvar x
  assume nfri.1: |- F/ x ph


  assert |- ( E. x ph -> A. x ph )

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
    nfri.1
    wph
    vx
    df-nf
    mpbi
end
