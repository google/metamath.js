include "cab.mm"
include "bj-nfsab1.mm"
include "nfci.mm"

theorem bj-nfab1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- F/_ x { x | ph }

  proof
    vx
    vy
    wph
    vx
    cab
    wph
    vx
    vy
    bj-nfsab1
    nfci
end
