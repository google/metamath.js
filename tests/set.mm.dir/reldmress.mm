include "cvv.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "cnx.mm"
include "cin.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cif.mm"
include "cress.mm"
include "df-ress.mm"
include "reldmmpt2.mm"

theorem reldmress
  let va: setvar a
  let vw: setvar w


  assert |- Rel dom |`s

  proof
    vw
    va
    cvv
    cvv
    vw
    cv
    #
    cbs
    cfv
    #
    va
    cv
    #
    wss
    @0
    @0
    cnx
    cbs
    cfv
    @2
    @1
    cin
    cop
    csts
    co
    cif
    cress
    va
    vw
    df-ress
    reldmmpt2
end
