include "c0.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wcel.mm"
include "wne.mm"
include "0pwfi.mm"
include "ne0i.mm"
include "ax-mp.mm"

theorem pwfin0
  let cA: class A


  assert |- ( ~P A i^i Fin ) =/= (/)

  proof
    c0
    cA
    cpw
    cfn
    cin
    #
    wcel
    @0
    c0
    wne
    cA
    0pwfi
    @0
    c0
    ne0i
    ax-mp
end
