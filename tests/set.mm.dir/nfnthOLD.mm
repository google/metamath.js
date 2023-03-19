include "wal.mm"
include "pm2.21i.mm"
include "nfiOLD.mm"

theorem nfnthOLD
  let wph: wff ph
  let vx: setvar x
  assume nfnthOLD.1: |- -. ph


  assert |- nfOLD x ph

  proof
    wph
    vx
    wph
    wph
    vx
    wal
    nfnthOLD.1
    pm2.21i
    nfiOLD
end
