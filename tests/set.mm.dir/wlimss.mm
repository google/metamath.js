include "cwlim.mm"
include "cv.mm"
include "cinf.mm"
include "wne.mm"
include "cpred.mm"
include "csup.mm"
include "wceq.mm"
include "wa.mm"
include "crab.mm"
include "df-wlim.mm"
include "ssrab2.mm"
include "eqsstri.mm"

theorem wlimss
  let cA: class A
  let cR: class R
  let vx: setvar x


  assert |- WLim ( R , A ) C_ A

  proof
    cA
    cR
    cwlim
    vx
    cv
    #
    cA
    cA
    cR
    cinf
    wne
    @0
    cA
    cR
    @0
    cpred
    cA
    cR
    csup
    wceq
    wa
    #
    vx
    cA
    crab
    cA
    vx
    cA
    cR
    df-wlim
    @1
    vx
    cA
    ssrab2
    eqsstri
end
