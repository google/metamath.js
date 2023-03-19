include "cwun.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cwunm.mm"
include "cfv.mm"
include "cv.mm"
include "crab.mm"
include "cint.mm"
include "cvv.mm"
include "wceq.mm"
include "ssexg.mm"
include "ancoms.mm"
include "wuncval.mm"
include "syl.mm"
include "sseq2.mm"
include "intminss.mm"
include "eqsstrd.mm"

theorem wuncss
  let cA: class A
  let cU: class U
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let vn: setvar n
  let cV: class V
  let cF: class F


  assert |- ( ( U e. WUni /\ A C_ U ) -> ( wUniCl ` A ) C_ U )

  proof
    cU
    cwun
    wcel
    #
    cA
    cU
    wss
    #
    wa
    #
    cA
    cwunm
    cfv
    #
    cA
    vu
    cv
    #
    wss
    #
    vu
    cwun
    crab
    cint
    #
    cU
    @2
    cA
    cvv
    wcel
    #
    @3
    @6
    wceq
    @1
    @0
    @7
    cA
    cU
    cwun
    ssexg
    ancoms
    vu
    cA
    cvv
    wuncval
    syl
    @5
    @1
    vu
    cU
    cwun
    @4
    cU
    cA
    sseq2
    intminss
    eqsstrd
end
