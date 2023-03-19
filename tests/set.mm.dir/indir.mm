include "cun.mm"
include "cin.mm"
include "indi.mm"
include "incom.mm"
include "uneq12i.mm"
include "3eqtr4i.mm"

theorem indir
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A u. B ) i^i C ) = ( ( A i^i C ) u. ( B i^i C ) )

  proof
    cC
    cA
    cB
    cun
    #
    cin
    cC
    cA
    cin
    #
    cC
    cB
    cin
    #
    cun
    @0
    cC
    cin
    cA
    cC
    cin
    #
    cB
    cC
    cin
    #
    cun
    cC
    cA
    cB
    indi
    @0
    cC
    incom
    @3
    @1
    @4
    @2
    cA
    cC
    incom
    cB
    cC
    incom
    uneq12i
    3eqtr4i
end
