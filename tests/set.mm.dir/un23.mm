include "cun.mm"
include "unass.mm"
include "un12.mm"
include "uncom.mm"
include "3eqtri.mm"

theorem un23
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A u. B ) u. C ) = ( ( A u. C ) u. B )

  proof
    cA
    cB
    cun
    cC
    cun
    cA
    cB
    cC
    cun
    cun
    cB
    cA
    cC
    cun
    #
    cun
    @0
    cB
    cun
    cA
    cB
    cC
    unass
    cA
    cB
    cC
    un12
    cB
    @0
    uncom
    3eqtri
end
