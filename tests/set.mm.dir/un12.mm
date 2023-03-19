include "cun.mm"
include "uncom.mm"
include "uneq1i.mm"
include "unass.mm"
include "3eqtr3i.mm"

theorem un12
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A u. ( B u. C ) ) = ( B u. ( A u. C ) )

  proof
    cA
    cB
    cun
    #
    cC
    cun
    cB
    cA
    cun
    #
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
    cun
    @0
    @1
    cC
    cA
    cB
    uncom
    uneq1i
    cA
    cB
    cC
    unass
    cB
    cA
    cC
    unass
    3eqtr3i
end
