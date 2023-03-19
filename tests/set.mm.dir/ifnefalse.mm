include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "cif.mm"
include "df-ne.mm"
include "iffalse.mm"
include "sylbi.mm"

theorem ifnefalse
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A =/= B -> if ( A = B , C , D ) = D )

  proof
    cA
    cB
    wne
    cA
    cB
    wceq
    #
    wn
    @0
    cC
    cD
    cif
    cD
    wceq
    cA
    cB
    df-ne
    @0
    cC
    cD
    iffalse
    sylbi
end
