include "con0.mm"
include "cale.mm"
include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wfn.mm"
include "wcel.mm"
include "alephfnon.mm"
include "alephon.mm"
include "rgenw.mm"
include "ffnfv.mm"
include "mpbir2an.mm"
include "wa.mm"
include "aleph11.mm"
include "biimpd.mm"
include "rgen2a.mm"
include "dff13.mm"

theorem alephf1
  let vx: setvar x
  let vy: setvar y


  assert |- aleph : On -1-1-> On

  proof
    con0
    con0
    cale
    wf1
    con0
    con0
    cale
    wf
    #
    vx
    cv
    #
    cale
    cfv
    #
    vy
    cv
    #
    cale
    cfv
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    con0
    wral
    vx
    con0
    wral
    @0
    cale
    con0
    wfn
    @2
    con0
    wcel
    #
    vx
    con0
    wral
    alephfnon
    @7
    vx
    con0
    @1
    alephon
    rgenw
    vx
    con0
    con0
    cale
    ffnfv
    mpbir2an
    @6
    vx
    vy
    con0
    @1
    con0
    wcel
    @3
    con0
    wcel
    wa
    @4
    @5
    @1
    @3
    aleph11
    biimpd
    rgen2a
    vx
    vy
    con0
    con0
    cale
    dff13
    mpbir2an
end
