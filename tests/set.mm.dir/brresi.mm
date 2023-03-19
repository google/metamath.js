include "cres.mm"
include "resss.mm"
include "ssbri.mm"

theorem brresi
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume brresi.1: |- B e. _V


  assert |- ( A ( R |` C ) B -> A R B )

  proof
    cR
    cC
    cres
    cR
    cA
    cB
    cR
    cC
    resss
    ssbri
end
