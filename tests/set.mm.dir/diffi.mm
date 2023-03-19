include "cfn.mm"
include "wcel.mm"
include "cdif.mm"
include "wss.mm"
include "difss.mm"
include "ssfi.mm"
include "mpan2.mm"

theorem diffi
  let cA: class A
  let cB: class B


  assert |- ( A e. Fin -> ( A \ B ) e. Fin )

  proof
    cA
    cfn
    wcel
    cA
    cB
    cdif
    #
    cA
    wss
    @0
    cfn
    wcel
    cA
    cB
    difss
    cA
    @0
    ssfi
    mpan2
end
