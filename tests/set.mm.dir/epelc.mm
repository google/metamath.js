include "cvv.mm"
include "wcel.mm"
include "cep.mm"
include "wbr.mm"
include "wb.mm"
include "epelg.mm"
include "ax-mp.mm"

theorem epelc
  let cA: class A
  let cB: class B
  assume epelc.1: |- B e. _V


  assert |- ( A _E B <-> A e. B )

  proof
    cB
    cvv
    wcel
    cA
    cB
    cep
    wbr
    cA
    cB
    wcel
    wb
    epelc.1
    cA
    cB
    cvv
    epelg
    ax-mp
end
