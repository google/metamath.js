include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "necon3abii.mm"
include "df-ne.mm"
include "bitr4i.mm"

theorem necon3bii
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume necon3bii.1: |- ( A = B <-> C = D )


  assert |- ( A =/= B <-> C =/= D )

  proof
    cA
    cB
    wne
    cC
    cD
    wceq
    #
    wn
    cC
    cD
    wne
    @0
    cA
    cB
    necon3bii.1
    necon3abii
    cC
    cD
    df-ne
    bitr4i
end
