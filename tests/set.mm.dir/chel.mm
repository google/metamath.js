include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "chss.mm"
include "sselda.mm"

theorem chel
  let cA: class A
  let cH: class H


  assert |- ( ( H e. CH /\ A e. H ) -> A e. ~H )

  proof
    cH
    cch
    wcel
    cH
    chil
    cA
    cH
    chss
    sselda
end
