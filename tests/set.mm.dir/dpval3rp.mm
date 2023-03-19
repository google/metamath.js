include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "rpre.mm"
include "ax-mp.mm"
include "dpval3.mm"

theorem dpval3rp
  let cA: class A
  let cB: class B
  assume dpval3rp.a: |- A e. NN0
  assume dpval3rp.b: |- B e. RR+


  assert |- ( A . B ) = _ A B

  proof
    cA
    cB
    dpval3rp.a
    cB
    crp
    wcel
    cB
    cr
    wcel
    dpval3rp.b
    cB
    rpre
    ax-mp
    dpval3
end
