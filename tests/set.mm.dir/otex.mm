include "cotp.mm"
include "cop.mm"
include "cvv.mm"
include "df-ot.mm"
include "opex.mm"
include "eqeltri.mm"

theorem otex
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- <. A , B , C >. e. _V

  proof
    cA
    cB
    cC
    cotp
    cA
    cB
    cop
    #
    cC
    cop
    cvv
    cA
    cB
    cC
    df-ot
    @0
    cC
    opex
    eqeltri
end
