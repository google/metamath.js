include "wex.mm"
include "nf5ri.mm"
include "hbexOLD.mm"
include "nf5i.mm"

theorem nfexOLD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume nfexOLD.1: |- F/ x ph


  assert |- F/ x E. y ph

  proof
    wph
    vy
    wex
    vx
    wph
    vx
    vy
    wph
    vx
    nfexOLD.1
    nf5ri
    hbexOLD
    nf5i
end
