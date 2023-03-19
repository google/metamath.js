include "cv.mm"
include "wbr.mm"
include "ccnv.mm"
include "df-cnv.mm"
include "relopabi.mm"

theorem relcnv
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- Rel `' A

  proof
    vy
    cv
    vx
    cv
    cA
    wbr
    vx
    vy
    cA
    ccnv
    vx
    vy
    cA
    df-cnv
    relopabi
end
