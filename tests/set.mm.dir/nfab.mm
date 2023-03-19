include "cab.mm"
include "nfsab.mm"
include "nfci.mm"

theorem nfab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume nfab.1: |- F/ x ph


  assert |- F/_ x { y | ph }

  proof
    vx
    vz
    wph
    vy
    cab
    wph
    vx
    vy
    vz
    nfab.1
    nfsab
    nfci
end
