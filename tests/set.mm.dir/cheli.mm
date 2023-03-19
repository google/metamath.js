include "chil.mm"
include "chssii.mm"
include "sseli.mm"

theorem cheli
  let cA: class A
  let cH: class H
  assume chssi.1: |- H e. CH


  assert |- ( A e. H -> A e. ~H )

  proof
    cH
    chil
    cA
    cH
    chssi.1
    chssii
    sseli
end
