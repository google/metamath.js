include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "ciun.mm"
include "rgenw.mm"
include "iunexg.mm"
include "mp2an.mm"

theorem iunex
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume iunex.1: |- A e. _V
  assume iunex.2: |- B e. _V

  disjoint A x
  assert |- U_ x e. A B e. _V

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    #
    vx
    cA
    wral
    vx
    cA
    cB
    ciun
    cvv
    wcel
    iunex.1
    @0
    vx
    cA
    iunex.2
    rgenw
    vx
    cA
    cB
    cvv
    cvv
    iunexg
    mp2an
end
