include "c0.mm"
include "bj-ctag.mm"
include "bj-0eltag.mm"
include "ne0ii.mm"

theorem bj-tagn0
  let cA: class A


  assert |- tag A =/= (/)

  proof
    c0
    cA
    bj-ctag
    cA
    bj-0eltag
    ne0ii
end
