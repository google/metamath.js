include "cz.mm"
include "cv.mm"
include "zcn.mm"
include "zaddcl.mm"
include "znegcl.mm"
include "1z.mm"
include "zmulcl.mm"
include "cnsubrglem.mm"

theorem zsubrg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R


  assert |- ZZ e. ( SubRing ` CCfld )

  proof
    vx
    vy
    cz
    vx
    cv
    #
    zcn
    @0
    vy
    cv
    #
    zaddcl
    @0
    znegcl
    1z
    @0
    @1
    zmulcl
    cnsubrglem
end
