include "wal.mm"
include "nfrdOLD.mm"
include "pm2.43i.mm"
include "nfiOLD.mm"

theorem nfdiOLD
  let wph: wff ph
  let vx: setvar x
  assume nfdiOLD.1: |- ( ph -> nfOLD x ph )


  assert |- nfOLD x ph

  proof
    wph
    vx
    wph
    wph
    vx
    wal
    wph
    wph
    vx
    nfdiOLD.1
    nfrdOLD
    pm2.43i
    nfiOLD
end
