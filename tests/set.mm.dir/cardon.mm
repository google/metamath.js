include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "wrex.mm"
include "cab.mm"
include "ccrd.mm"
include "cardf2.mm"
include "0elon.mm"
include "f0cli.mm"

theorem cardon
  let cA: class A
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B


  assert |- ( card ` A ) e. On

  proof
    vy
    cv
    vx
    cv
    cen
    wbr
    vy
    con0
    wrex
    vx
    cab
    con0
    cA
    ccrd
    vx
    vy
    cardf2
    0elon
    f0cli
end
