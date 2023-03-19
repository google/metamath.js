include "cun.mm"
include "unidm.mm"
include "uneq1i.mm"
include "un4.mm"
include "eqtr3i.mm"

theorem unundi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A u. ( B u. C ) ) = ( ( A u. B ) u. ( A u. C ) )

  proof
    cA
    cA
    cun
    #
    cB
    cC
    cun
    #
    cun
    cA
    @1
    cun
    cA
    cB
    cun
    cA
    cC
    cun
    cun
    @0
    cA
    @1
    cA
    unidm
    uneq1i
    cA
    cA
    cB
    cC
    un4
    eqtr3i
end
