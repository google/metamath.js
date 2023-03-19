include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mulid1.mm"
include "ax-mp.mm"

theorem mulid1i
  let cA: class A
  assume axi.1: |- A e. CC


  assert |- ( A x. 1 ) = A

  proof
    cA
    cc
    wcel
    cA
    c1
    cmul
    co
    cA
    wceq
    axi.1
    cA
    mulid1
    ax-mp
end
