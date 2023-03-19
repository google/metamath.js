include "chil.mm"
include "shssii.mm"
include "sseli.mm"

theorem sheli
  let cA: class A
  let cH: class H
  assume shssi.1: |- H e. SH


  assert |- ( A e. H -> A e. ~H )

  proof
    cH
    chil
    cA
    cH
    shssi.1
    shssii
    sseli
end
