include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wne.mm"
include "eldifsn.mm"
include "simprbi.mm"

theorem eldifsni
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B \ { C } ) -> A =/= C )

  proof
    cA
    cB
    cC
    csn
    cdif
    wcel
    cA
    cB
    wcel
    cA
    cC
    wne
    cA
    cB
    cC
    eldifsn
    simprbi
end
