include "wnfOLD.mm"
include "wal.mm"
include "wi.mm"
include "df-nfOLD.mm"
include "mpgbir.mm"

theorem nfiOLD
  let wph: wff ph
  let vx: setvar x
  assume nfiOLD.1: |- ( ph -> A. x ph )


  assert |- nfOLD x ph

  proof
    wph
    vx
    wnfOLD
    wph
    wph
    vx
    wal
    wi
    vx
    wph
    vx
    df-nfOLD
    nfiOLD.1
    mpgbir
end
