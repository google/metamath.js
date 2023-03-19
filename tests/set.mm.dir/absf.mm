include "cc.mm"
include "cr.mm"
include "cv.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "cabs.mm"
include "df-abs.mm"
include "wcel.mm"
include "absval.mm"
include "abscl.mm"
include "eqeltrrd.mm"
include "fmpti.mm"

theorem absf
  let cA: class A
  let vx: setvar x
  let cB: class B


  assert |- abs : CC --> RR

  proof
    vx
    cc
    cr
    vx
    cv
    #
    @0
    ccj
    cfv
    cmul
    co
    csqrt
    cfv
    #
    cabs
    vx
    df-abs
    @0
    cc
    wcel
    @0
    cabs
    cfv
    @1
    cr
    @0
    absval
    @0
    abscl
    eqeltrrd
    fmpti
end
