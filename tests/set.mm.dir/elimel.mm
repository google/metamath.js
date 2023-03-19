include "wcel.mm"
include "cif.mm"
include "eleq1.mm"
include "elimhyp.mm"

theorem elimel
  let cA: class A
  let cB: class B
  let cC: class C
  assume elimel.1: |- B e. C


  assert |- if ( A e. C , A , B ) e. C

  proof
    cA
    cC
    wcel
    #
    @0
    cA
    cB
    cif
    #
    cC
    wcel
    cB
    cC
    wcel
    cA
    cB
    cA
    @1
    cC
    eleq1
    cB
    @1
    cC
    eleq1
    elimel.1
    elimhyp
end
