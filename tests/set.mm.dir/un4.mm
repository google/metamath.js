include "cun.mm"
include "un12.mm"
include "uneq2i.mm"
include "unass.mm"
include "3eqtr4i.mm"

theorem un4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A u. B ) u. ( C u. D ) ) = ( ( A u. C ) u. ( B u. D ) )

  proof
    cA
    cB
    cC
    cD
    cun
    #
    cun
    #
    cun
    cA
    cC
    cB
    cD
    cun
    #
    cun
    #
    cun
    cA
    cB
    cun
    @0
    cun
    cA
    cC
    cun
    @2
    cun
    @1
    @3
    cA
    cB
    cC
    cD
    un12
    uneq2i
    cA
    cB
    @0
    unass
    cA
    cC
    @2
    unass
    3eqtr4i
end
