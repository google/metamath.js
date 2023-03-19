include "csur.mm"
include "wcel.mm"
include "cv.mm"
include "c1o.mm"
include "c2o.mm"
include "cpr.mm"
include "wf.mm"
include "con0.mm"
include "wrex.mm"
include "cdm.mm"
include "elno.mm"
include "fdm.mm"
include "eleq1d.mm"
include "biimprcd.mm"
include "rexlimiv.mm"
include "sylbi.mm"

theorem nodmon
  let cA: class A
  let vx: setvar x


  assert |- ( A e. No -> dom A e. On )

  proof
    cA
    csur
    wcel
    vx
    cv
    #
    c1o
    c2o
    cpr
    #
    cA
    wf
    #
    vx
    con0
    wrex
    cA
    cdm
    #
    con0
    wcel
    #
    vx
    cA
    elno
    @2
    @4
    vx
    con0
    @2
    @4
    @0
    con0
    wcel
    @2
    @3
    @0
    con0
    @0
    @1
    cA
    fdm
    eleq1d
    biimprcd
    rexlimiv
    sylbi
end
