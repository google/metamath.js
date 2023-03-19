include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "ccoss.mm"
include "df-coss.mm"
include "relopabi.mm"

theorem relcoss
  let cR: class R
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y


  assert |- Rel ,~ R

  proof
    vu
    cv
    #
    vx
    cv
    cR
    wbr
    @0
    vy
    cv
    cR
    wbr
    wa
    vu
    wex
    vx
    vy
    cR
    ccoss
    vx
    vy
    vu
    cR
    df-coss
    relopabi
end
