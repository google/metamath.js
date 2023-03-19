include "con0.mm"
include "cale.mm"
include "wf.mm"
include "wsmo.mm"
include "wf1.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "alephfnon.mm"
include "alephon.mm"
include "a1i.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"
include "alephsmo.mm"
include "smo11.mm"
include "mp2an.mm"

theorem alephf1ALT
  let vx: setvar x


  assert |- aleph : On -1-1-> On

  proof
    con0
    con0
    cale
    wf
    #
    cale
    wsmo
    con0
    con0
    cale
    wf1
    @0
    cale
    con0
    wfn
    vx
    cv
    #
    cale
    cfv
    con0
    wcel
    #
    vx
    con0
    wral
    alephfnon
    @2
    vx
    con0
    @2
    @1
    con0
    wcel
    @1
    alephon
    a1i
    rgen
    vx
    con0
    con0
    cale
    ffnfv
    mpbir2an
    alephsmo
    con0
    con0
    cale
    smo11
    mp2an
end
