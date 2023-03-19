include "weq.mm"
include "wn.mm"
include "cab.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "crab.mm"
include "pm3.24.mm"
include "equid.mm"
include "2th.mm"
include "con1bii.mm"
include "abbii.mm"
include "dfnul2.mm"
include "df-rab.mm"
include "3eqtr4i.mm"

theorem dfnul3
  let vx: setvar x
  let cA: class A


  assert |- (/) = { x e. A | -. x e. A }

  proof
    vx
    vx
    weq
    #
    wn
    #
    vx
    cab
    vx
    cv
    cA
    wcel
    #
    @2
    wn
    #
    wa
    #
    vx
    cab
    c0
    @3
    vx
    cA
    crab
    @1
    @4
    vx
    @4
    @0
    @4
    wn
    @0
    @2
    pm3.24
    vx
    equid
    2th
    con1bii
    abbii
    vx
    dfnul2
    @3
    vx
    cA
    df-rab
    3eqtr4i
end
