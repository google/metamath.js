include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "inss1.mm"
include "eqsstri.mm"

theorem 3oalem4
  let cA: class A
  let cB: class B
  let cR: class R
  assume 3oalem4.3: |- R = ( ( _|_ ` B ) i^i ( B vH A ) )


  assert |- R C_ ( _|_ ` B )

  proof
    cR
    cB
    cort
    cfv
    #
    cB
    cA
    chj
    co
    #
    cin
    @0
    3oalem4.3
    @0
    @1
    inss1
    eqsstri
end
