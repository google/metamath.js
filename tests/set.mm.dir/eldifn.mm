include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "eldif.mm"
include "simprbi.mm"

theorem eldifn
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B \ C ) -> -. A e. C )

  proof
    cA
    cB
    cC
    cdif
    wcel
    cA
    cB
    wcel
    cA
    cC
    wcel
    wn
    cA
    cB
    cC
    eldif
    simprbi
end
