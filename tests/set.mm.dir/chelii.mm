include "chil.mm"
include "chssii.mm"
include "sselii.mm"

theorem chelii
  let cA: class A
  let cH: class H
  assume chssi.1: |- H e. CH
  assume cheli.1: |- A e. H


  assert |- A e. ~H

  proof
    cH
    chil
    cA
    cH
    chssi.1
    chssii
    cheli.1
    sselii
end
