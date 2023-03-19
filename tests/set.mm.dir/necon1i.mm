include "wceq.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "sylbir.mm"
include "necon1ai.mm"

theorem necon1i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume necon1i.1: |- ( A =/= B -> C = D )


  assert |- ( C =/= D -> A = B )

  proof
    cA
    cB
    wceq
    #
    cC
    cD
    @0
    wn
    cA
    cB
    wne
    cC
    cD
    wceq
    cA
    cB
    df-ne
    necon1i.1
    sylbir
    necon1ai
end
