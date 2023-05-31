include "cv.mm"
include "cab.mm"
include "wcel.mm"
include "hbab1.mm"
include "nf5i.mm"

theorem nfsab1
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y

  disjoint x y
  assert |- F/ x y e. { x | ph }

  proof
    vy
    cv
    wph
    vx
    cab
    wcel
    vx
    wph
    vx
    vy
    hbab1
    nf5i
end
