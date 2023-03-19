include "wnfOLD.mm"
include "wal.mm"
include "wi.mm"
include "nfrOLD.mm"
include "ax-mp.mm"

theorem nfriOLD
  let wph: wff ph
  let vx: setvar x
  assume nfriOLD.1: |- nfOLD x ph


  assert |- ( ph -> A. x ph )

  proof
    wph
    vx
    wnfOLD
    wph
    wph
    vx
    wal
    wi
    nfriOLD.1
    wph
    vx
    nfrOLD
    ax-mp
end
