include "csur.mm"
include "wcel.mm"
include "cv.mm"
include "c1o.mm"
include "c2o.mm"
include "cpr.mm"
include "wf.mm"
include "con0.mm"
include "wrex.mm"
include "wfun.mm"
include "elno.mm"
include "ffun.mm"
include "rexlimivw.mm"
include "sylbi.mm"

theorem nofun
  let cA: class A
  let vx: setvar x


  assert |- ( A e. No -> Fun A )

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
    wfun
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
    ffun
    rexlimivw
    sylbi
end
