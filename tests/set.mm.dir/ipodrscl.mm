include "cipo.mm"
include "cfv.mm"
include "cdrs.mm"
include "wcel.mm"
include "cvv.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cun.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "isipodrs.mm"
include "simp1bi.mm"

theorem ipodrscl
  let cA: class A
  let vw: setvar w
  let vz: setvar z
  let vx: setvar x
  let vy: setvar y
  let cX: class X


  assert |- ( ( toInc ` A ) e. Dirset -> A e. _V )

  proof
    cA
    cipo
    cfv
    cdrs
    wcel
    cA
    cvv
    wcel
    cA
    c0
    wne
    vx
    cv
    vy
    cv
    cun
    vz
    cv
    wss
    vz
    cA
    wrex
    vy
    cA
    wral
    vx
    cA
    wral
    vx
    vy
    vz
    cA
    isipodrs
    simp1bi
end
