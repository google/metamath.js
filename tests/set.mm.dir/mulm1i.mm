include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mulm1.mm"
include "ax-mp.mm"

theorem mulm1i
  let cA: class A
  assume mulm1.1: |- A e. CC


  assert |- ( -u 1 x. A ) = -u A

  proof
    cA
    cc
    wcel
    c1
    cneg
    cA
    cmul
    co
    cA
    cneg
    wceq
    mulm1.1
    cA
    mulm1
    ax-mp
end
