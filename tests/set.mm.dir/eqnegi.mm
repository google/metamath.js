include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "wceq.mm"
include "cc0.mm"
include "wb.mm"
include "eqneg.mm"
include "ax-mp.mm"

theorem eqnegi
  let cA: class A
  assume divclz.1: |- A e. CC


  assert |- ( A = -u A <-> A = 0 )

  proof
    cA
    cc
    wcel
    cA
    cA
    cneg
    wceq
    cA
    cc0
    wceq
    wb
    divclz.1
    cA
    eqneg
    ax-mp
end
