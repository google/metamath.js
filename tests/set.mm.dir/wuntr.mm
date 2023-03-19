include "cwun.mm"
include "wcel.mm"
include "wtr.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cuni.mm"
include "cpw.mm"
include "cpr.mm"
include "wral.mm"
include "w3a.mm"
include "iswun.mm"
include "ibi.mm"
include "simp1d.mm"

theorem wuntr
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vu: setvar u


  assert |- ( U e. WUni -> Tr U )

  proof
    cU
    cwun
    wcel
    #
    cU
    wtr
    #
    cU
    c0
    wne
    #
    vx
    cv
    #
    cuni
    cU
    wcel
    @3
    cpw
    cU
    wcel
    @3
    vy
    cv
    cpr
    cU
    wcel
    vy
    cU
    wral
    w3a
    vx
    cU
    wral
    #
    @0
    @1
    @2
    @4
    w3a
    vx
    vy
    cU
    cwun
    iswun
    ibi
    simp1d
end
