include "wcel.mm"
include "cwunm.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "cwun.mm"
include "crab.mm"
include "cint.mm"
include "wuncval.mm"
include "c0.mm"
include "wne.mm"
include "ssrab2.mm"
include "wrex.mm"
include "wunex.mm"
include "rabn0.mm"
include "sylibr.mm"
include "intwun.mm"
include "sylancr.mm"
include "eqeltrd.mm"

theorem wunccl
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


  assert |- ( A e. V -> ( wUniCl ` A ) e. WUni )

  proof
    cA
    cV
    wcel
    #
    cA
    cwunm
    cfv
    cA
    vu
    cv
    wss
    #
    vu
    cwun
    crab
    #
    cint
    #
    cwun
    vu
    cA
    cV
    wuncval
    @0
    @2
    cwun
    wss
    @2
    c0
    wne
    #
    @3
    cwun
    wcel
    @1
    vu
    cwun
    ssrab2
    @0
    @1
    vu
    cwun
    wrex
    @4
    vu
    cA
    cV
    wunex
    @1
    vu
    cwun
    rabn0
    sylibr
    @2
    intwun
    sylancr
    eqeltrd
end
