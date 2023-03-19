include "cin.mm"
include "cres.mm"
include "incom.mm"
include "reseq2i.mm"
include "resres.mm"
include "3eqtr4i.mm"

theorem rescom
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A |` B ) |` C ) = ( ( A |` C ) |` B )

  proof
    cA
    cB
    cC
    cin
    #
    cres
    cA
    cC
    cB
    cin
    #
    cres
    cA
    cB
    cres
    cC
    cres
    cA
    cC
    cres
    cB
    cres
    @0
    @1
    cA
    cB
    cC
    incom
    reseq2i
    cA
    cB
    cC
    resres
    cA
    cC
    cB
    resres
    3eqtr4i
end
