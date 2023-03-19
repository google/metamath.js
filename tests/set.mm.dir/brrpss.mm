include "cvv.mm"
include "wcel.mm"
include "crpss.mm"
include "wbr.mm"
include "wpss.mm"
include "wb.mm"
include "brrpssg.mm"
include "ax-mp.mm"

theorem brrpss
  let cA: class A
  let cB: class B
  assume brrpss.a: |- B e. _V


  assert |- ( A [C.] B <-> A C. B )

  proof
    cB
    cvv
    wcel
    cA
    cB
    crpss
    wbr
    cA
    cB
    wpss
    wb
    brrpss.a
    cA
    cB
    cvv
    brrpssg
    ax-mp
end
