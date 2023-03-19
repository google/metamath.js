include "cvv.mm"
include "cv.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "wss.mm"
include "cnx.mm"
include "cress.mm"
include "co.mm"
include "cop.mm"
include "csts.mm"
include "cif.mm"
include "cresv.mm"
include "df-resv.mm"
include "reldmmpt2.mm"

theorem reldmresv
  let vx: setvar x
  let vy: setvar y


  assert |- Rel dom |`v

  proof
    vy
    vx
    cvv
    cvv
    vy
    cv
    #
    csca
    cfv
    #
    cbs
    cfv
    vx
    cv
    #
    wss
    @0
    @0
    cnx
    csca
    cfv
    @1
    @2
    cress
    co
    cop
    csts
    co
    cif
    cresv
    vx
    vy
    df-resv
    reldmmpt2
end
