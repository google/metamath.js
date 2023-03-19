include "wcel.mm"
include "cec.mm"
include "csn.mm"
include "cima.mm"
include "cv.mm"
include "wbr.mm"
include "cab.mm"
include "df-ec.mm"
include "imasng.mm"
include "syl5eq.mm"

theorem dfec2
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cV: class V

  disjoint A y
  disjoint R y
  assert |- ( A e. V -> [ A ] R = { y | A R y } )

  proof
    cA
    cV
    wcel
    cA
    cR
    cec
    cR
    cA
    csn
    cima
    cA
    vy
    cv
    cR
    wbr
    vy
    cab
    cA
    cR
    df-ec
    vy
    cA
    cV
    cR
    imasng
    syl5eq
end
