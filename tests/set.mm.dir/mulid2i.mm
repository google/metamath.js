include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mulid2.mm"
include "ax-mp.mm"

theorem mulid2i
  let cA: class A
  assume axi.1: |- A e. CC


  assert |- ( 1 x. A ) = A

  proof
    cA
    cc
    wcel
    c1
    cA
    cmul
    co
    cA
    wceq
    axi.1
    cA
    mulid2
    ax-mp
end
