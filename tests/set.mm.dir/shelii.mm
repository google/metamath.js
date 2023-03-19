include "chil.mm"
include "shssii.mm"
include "sselii.mm"

theorem shelii
  let cA: class A
  let cH: class H
  assume shssi.1: |- H e. SH
  assume sheli.1: |- A e. H


  assert |- A e. ~H

  proof
    cH
    chil
    cA
    cH
    shssi.1
    shssii
    sheli.1
    sselii
end
