include "com.mm"
include "cv.mm"
include "wlim.mm"
include "wn.mm"
include "con0.mm"
include "crab.mm"
include "wss.mm"
include "wral.mm"
include "omsson.mm"
include "nnlim.mm"
include "rgen.mm"
include "ssrab.mm"
include "mpbir2an.mm"

theorem omssnlim
  let vx: setvar x
  let cA: class A


  assert |- _om C_ { x e. On | -. Lim x }

  proof
    com
    vx
    cv
    #
    wlim
    wn
    #
    vx
    con0
    crab
    wss
    com
    con0
    wss
    @1
    vx
    com
    wral
    omsson
    @1
    vx
    com
    @0
    nnlim
    rgen
    @1
    vx
    con0
    com
    ssrab
    mpbir2an
end
