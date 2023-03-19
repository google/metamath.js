include "cha.mm"
include "haustop.mm"
include "cv.mm"
include "cuni.mm"
include "cnhaus.mm"
include "haushmphlem.mm"

theorem haushmph
  let cJ: class J
  let cK: class K
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( J ~= K -> ( J e. Haus -> K e. Haus ) )

  proof
    cha
    vf
    cJ
    cK
    cJ
    haustop
    vf
    cv
    cK
    cJ
    cK
    cuni
    cJ
    cuni
    cnhaus
    haushmphlem
end
