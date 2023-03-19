include "cun.mm"
include "unidm.mm"
include "uneq2i.mm"
include "un4.mm"
include "eqtr3i.mm"

theorem unundir
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A u. B ) u. C ) = ( ( A u. C ) u. ( B u. C ) )

  proof
    cA
    cB
    cun
    #
    cC
    cC
    cun
    #
    cun
    @0
    cC
    cun
    cA
    cC
    cun
    cB
    cC
    cun
    cun
    @1
    cC
    @0
    cC
    unidm
    uneq2i
    cA
    cB
    cC
    cC
    un4
    eqtr3i
end
