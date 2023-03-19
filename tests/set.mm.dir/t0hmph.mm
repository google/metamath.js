include "ct0.mm"
include "t0top.mm"
include "cv.mm"
include "cuni.mm"
include "cnt0.mm"
include "haushmphlem.mm"

theorem t0hmph
  let cJ: class J
  let cK: class K
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( J ~= K -> ( J e. Kol2 -> K e. Kol2 ) )

  proof
    ct0
    vf
    cJ
    cK
    cJ
    t0top
    vf
    cv
    cK
    cJ
    cK
    cuni
    cJ
    cuni
    cnt0
    haushmphlem
end
