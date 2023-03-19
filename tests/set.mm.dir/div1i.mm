include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "div1.mm"
include "ax-mp.mm"

theorem div1i
  let cA: class A
  assume divclz.1: |- A e. CC


  assert |- ( A / 1 ) = A

  proof
    cA
    cc
    wcel
    cA
    c1
    cdiv
    co
    cA
    wceq
    divclz.1
    cA
    div1
    ax-mp
end
