include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "subid.mm"
include "ax-mp.mm"

theorem subidi
  let cA: class A
  assume negidi.1: |- A e. CC


  assert |- ( A - A ) = 0

  proof
    cA
    cc
    wcel
    cA
    cA
    cmin
    co
    cc0
    wceq
    negidi.1
    cA
    subid
    ax-mp
end
