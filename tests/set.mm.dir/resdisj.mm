include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cres.mm"
include "reseq2.mm"
include "resres.mm"
include "res0.mm"
include "eqcomi.mm"
include "3eqtr4g.mm"

theorem resdisj
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A i^i B ) = (/) -> ( ( C |` A ) |` B ) = (/) )

  proof
    cA
    cB
    cin
    #
    c0
    wceq
    cC
    @0
    cres
    cC
    c0
    cres
    #
    cC
    cA
    cres
    cB
    cres
    c0
    @0
    c0
    cC
    reseq2
    cC
    cA
    cB
    resres
    @1
    c0
    cC
    res0
    eqcomi
    3eqtr4g
end
