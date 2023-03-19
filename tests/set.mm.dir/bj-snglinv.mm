include "cv.mm"
include "csn.mm"
include "bj-csngl.mm"
include "wcel.mm"
include "bj-snglc.mm"
include "abbi2i.mm"

theorem bj-snglinv
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- A = { x | { x } e. sngl A }

  proof
    vx
    cv
    #
    csn
    cA
    bj-csngl
    wcel
    vx
    cA
    @0
    cA
    bj-snglc
    abbi2i
end
