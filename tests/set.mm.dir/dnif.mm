include "cr.mm"
include "cv.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "cabs.mm"
include "wcel.mm"
include "id.mm"
include "dnicld1.mm"
include "fmpti.mm"

theorem dnif
  let vx: setvar x
  let cT: class T
  assume dnif.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )


  assert |- T : RR --> RR

  proof
    vx
    cr
    cr
    vx
    cv
    #
    c1
    c2
    cdiv
    co
    caddc
    co
    cfl
    cfv
    @0
    cmin
    co
    cabs
    cfv
    cT
    dnif.t
    @0
    cr
    wcel
    #
    @0
    @1
    id
    dnicld1
    fmpti
end
