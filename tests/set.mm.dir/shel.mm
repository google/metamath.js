include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "shss.mm"
include "sselda.mm"

theorem shel
  let cA: class A
  let cH: class H


  assert |- ( ( H e. SH /\ A e. H ) -> A e. ~H )

  proof
    cH
    csh
    wcel
    cH
    chil
    cA
    cH
    shss
    sselda
end
