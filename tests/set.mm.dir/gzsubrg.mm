include "cgz.mm"
include "cv.mm"
include "gzcn.mm"
include "gzaddcl.mm"
include "gznegcl.mm"
include "c1.mm"
include "cz.mm"
include "wcel.mm"
include "1z.mm"
include "zgz.mm"
include "ax-mp.mm"
include "gzmulcl.mm"
include "cnsubrglem.mm"

theorem gzsubrg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R


  assert |- Z[i] e. ( SubRing ` CCfld )

  proof
    vx
    vy
    cgz
    vx
    cv
    #
    gzcn
    @0
    vy
    cv
    #
    gzaddcl
    @0
    gznegcl
    c1
    cz
    wcel
    c1
    cgz
    wcel
    1z
    c1
    zgz
    ax-mp
    @0
    @1
    gzmulcl
    cnsubrglem
end
