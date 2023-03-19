include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "wdisj.mm"
include "wtru.mm"
include "sndisj.mm"
include "a1i.mm"
include "disjxp1.mm"
include "trud.mm"

theorem disjsnxp
  let cA: class A
  let cB: class B
  let vj: setvar j

  disjoint A j
  assert |- Disj_ j e. A ( { j } X. B )

  proof
    vj
    cA
    vj
    cv
    csn
    #
    cB
    cxp
    wdisj
    wtru
    vj
    cA
    @0
    cB
    vj
    cA
    @0
    wdisj
    wtru
    vj
    cA
    sndisj
    a1i
    disjxp1
    trud
end
