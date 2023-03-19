include "c2.mm"
include "cn0.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmpt.mm"
include "ccn.mm"
include "2nn0.mm"
include "expcn.mm"
include "ax-mp.mm"

theorem sqcn
  let vx: setvar x
  let cJ: class J
  assume sqcn.j: |- J = ( TopOpen ` CCfld )

  disjoint J x
  assert |- ( x e. CC |-> ( x ^ 2 ) ) e. ( J Cn J )

  proof
    c2
    cn0
    wcel
    vx
    cc
    vx
    cv
    c2
    cexp
    co
    cmpt
    cJ
    cJ
    ccn
    co
    wcel
    2nn0
    vx
    cJ
    c2
    sqcn.j
    expcn
    ax-mp
end
