include "wac.mm"
include "cv.mm"
include "cpw.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "con0.mm"
include "wral.mm"
include "cale.mm"
include "cfv.mm"
include "dfac12a.mm"
include "dfac12k.mm"
include "bitri.mm"

theorem dfac12
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z


  assert |- ( CHOICE <-> A. x e. On ~P ( aleph ` x ) e. dom card )

  proof
    wac
    vy
    cv
    cpw
    ccrd
    cdm
    #
    wcel
    vy
    con0
    wral
    vx
    cv
    cale
    cfv
    cpw
    @0
    wcel
    vx
    con0
    wral
    vy
    dfac12a
    vy
    vx
    dfac12k
    bitri
end
