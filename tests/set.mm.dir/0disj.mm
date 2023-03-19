include "c0.mm"
include "cv.mm"
include "csn.mm"
include "wss.mm"
include "wral.mm"
include "wdisj.mm"
include "0ss.mm"
include "rgenw.mm"
include "sndisj.mm"
include "disjss2.mm"
include "mp2.mm"

theorem 0disj
  let vx: setvar x
  let cA: class A


  assert |- Disj_ x e. A (/)

  proof
    c0
    vx
    cv
    csn
    #
    wss
    #
    vx
    cA
    wral
    vx
    cA
    @0
    wdisj
    vx
    cA
    c0
    wdisj
    @1
    vx
    cA
    @0
    0ss
    rgenw
    vx
    cA
    sndisj
    vx
    cA
    c0
    @0
    disjss2
    mp2
end
