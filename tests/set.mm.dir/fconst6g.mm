include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "fconstg.mm"
include "snssi.mm"
include "fssd.mm"

theorem fconst6g
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( B e. C -> ( A X. { B } ) : A --> C )

  proof
    cB
    cC
    wcel
    cA
    cB
    csn
    #
    cC
    cA
    @0
    cxp
    cA
    cB
    cC
    fconstg
    cB
    cC
    snssi
    fssd
end
