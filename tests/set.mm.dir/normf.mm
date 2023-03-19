include "chil.mm"
include "cr.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "cno.mm"
include "dfhnorm2.mm"
include "wcel.mm"
include "hiidrcl.mm"
include "hiidge0.mm"
include "resqrtcld.mm"
include "fmpti.mm"

theorem normf
  let vx: setvar x


  assert |- normh : ~H --> RR

  proof
    vx
    chil
    cr
    vx
    cv
    #
    @0
    csp
    co
    #
    csqrt
    cfv
    cno
    vx
    dfhnorm2
    @0
    chil
    wcel
    @1
    @0
    hiidrcl
    @0
    hiidge0
    resqrtcld
    fmpti
end
