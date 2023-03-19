include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "cwun.mm"
include "crab.mm"
include "cint.mm"
include "cwunm.mm"
include "cfv.mm"
include "ssintub.mm"
include "wuncval.mm"
include "syl5sseqr.mm"

theorem wuncid
  let cA: class A
  let cV: class V
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let vn: setvar n
  let cU: class U
  let cF: class F


  assert |- ( A e. V -> A C_ ( wUniCl ` A ) )

  proof
    cA
    cV
    wcel
    cA
    vu
    cv
    wss
    vu
    cwun
    crab
    cint
    cA
    cA
    cwunm
    cfv
    vu
    cA
    cwun
    ssintub
    vu
    cA
    cV
    wuncval
    syl5sseqr
end
