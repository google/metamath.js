include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "subid1.mm"
include "ax-mp.mm"

theorem subid1i
  let cA: class A
  assume negidi.1: |- A e. CC


  assert |- ( A - 0 ) = A

  proof
    cA
    cc
    wcel
    cA
    cc0
    cmin
    co
    cA
    wceq
    negidi.1
    cA
    subid1
    ax-mp
end
