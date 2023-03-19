include "wal.mm"
include "nf5ri.mm"
include "hbal.mm"
include "nf5i.mm"

theorem nfal
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume nfal.1: |- F/ x ph


  assert |- F/ x A. y ph

  proof
    wph
    vy
    wal
    vx
    wph
    vx
    vy
    wph
    vx
    nfal.1
    nf5ri
    hbal
    nf5i
end
