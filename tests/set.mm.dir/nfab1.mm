include "cab.mm"
include "nfsab1.mm"
include "nfci.mm"

theorem nfab1
  param wph: wff ph
  param vx: setvar x
  let vy: setvar y
  let cA: class A


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
    nfsab1
    nfci
end
