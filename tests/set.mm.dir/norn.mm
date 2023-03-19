include "csur.mm"
include "wcel.mm"
include "cv.mm"
include "c1o.mm"
include "c2o.mm"
include "cpr.mm"
include "wf.mm"
include "con0.mm"
include "wrex.mm"
include "crn.mm"
include "wss.mm"
include "elno.mm"
include "frn.mm"
include "rexlimivw.mm"
include "sylbi.mm"

theorem norn
  let cA: class A
  let vx: setvar x


  assert |- ( A e. No -> ran A C_ { 1o , 2o } )

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
    crn
    @1
    wss
    #
    vx
    cA
    elno
    @2
    @3
    vx
    con0
    @0
    @1
    cA
    frn
    rexlimivw
    sylbi
end
