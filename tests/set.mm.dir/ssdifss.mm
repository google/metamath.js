include "cdif.mm"
include "wss.mm"
include "difss.mm"
include "sstr.mm"
include "mpan.mm"

theorem ssdifss
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A C_ B -> ( A \ C ) C_ B )

  proof
    cA
    cC
    cdif
    #
    cA
    wss
    cA
    cB
    wss
    @0
    cB
    wss
    cA
    cC
    difss
    @0
    cA
    cB
    sstr
    mpan
end
