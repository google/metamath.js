include "cq.mm"
include "cv.mm"
include "qcn.mm"
include "qaddcl.mm"
include "qnegcl.mm"
include "cz.mm"
include "c1.mm"
include "zssq.mm"
include "1z.mm"
include "sselii.mm"
include "qmulcl.mm"
include "qreccl.mm"
include "cnsubdrglem.mm"

theorem qsubdrg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R


  assert |- ( QQ e. ( SubRing ` CCfld ) /\ ( CCfld |`s QQ ) e. DivRing )

  proof
    vx
    vy
    cq
    vx
    cv
    #
    qcn
    @0
    vy
    cv
    #
    qaddcl
    @0
    qnegcl
    cz
    cq
    c1
    zssq
    1z
    sselii
    @0
    @1
    qmulcl
    @0
    qreccl
    cnsubdrglem
end
