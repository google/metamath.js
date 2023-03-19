include "cv.mm"
include "ccoss.mm"
include "cdm.mm"
include "wcel.mm"
include "wral.mm"
include "wbr.mm"
include "ralel.mm"
include "wb.mm"
include "cvv.mm"
include "eldmcoss2.mm"
include "elv.mm"
include "ralbii.mm"
include "mpbi.mm"

theorem refrelcosslem
  let vx: setvar x
  let cR: class R


  assert |- A. x e. dom ,~ R x ,~ R x

  proof
    vx
    cv
    #
    cR
    ccoss
    #
    cdm
    #
    wcel
    #
    vx
    @2
    wral
    @0
    @0
    @1
    wbr
    #
    vx
    @2
    wral
    vx
    @2
    ralel
    @3
    @4
    vx
    @2
    @3
    @4
    wb
    vx
    @0
    cR
    cvv
    eldmcoss2
    elv
    ralbii
    mpbi
end
