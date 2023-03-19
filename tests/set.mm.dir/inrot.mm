include "cin.mm"
include "in31.mm"
include "in32.mm"
include "eqtri.mm"

theorem inrot
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A i^i B ) i^i C ) = ( ( C i^i A ) i^i B )

  proof
    cA
    cB
    cin
    cC
    cin
    cC
    cB
    cin
    cA
    cin
    cC
    cA
    cin
    cB
    cin
    cA
    cB
    cC
    in31
    cC
    cB
    cA
    in32
    eqtri
end
