include "cvv.mm"
include "cv.mm"
include "cnx.mm"
include "cplusg.mm"
include "cfv.mm"
include "cmulr.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cmgp.mm"
include "ovex.mm"
include "df-mgp.mm"
include "fnmpti.mm"

theorem fnmgp
  let vx: setvar x


  assert |- mulGrp Fn _V

  proof
    vx
    cvv
    vx
    cv
    #
    cnx
    cplusg
    cfv
    @0
    cmulr
    cfv
    cop
    #
    csts
    co
    cmgp
    @0
    @1
    csts
    ovex
    vx
    df-mgp
    fnmpti
end
