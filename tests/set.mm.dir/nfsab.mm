include "cv.mm"
include "cab.mm"
include "wcel.mm"
include "nf5ri.mm"
include "hbab.mm"
include "nf5i.mm"

theorem nfsab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume nfsab.1: |- F/ x ph

  disjoint x z
  assert |- F/ x z e. { y | ph }

  proof
    vz
    cv
    wph
    vy
    cab
    wcel
    vx
    wph
    vx
    vy
    vz
    wph
    vx
    nfsab.1
    nf5ri
    hbab
    nf5i
end
