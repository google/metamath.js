include "chil.mm"
include "chj.mm"
include "co.mm"
include "cort.mm"
include "cfv.mm"
include "chj1i.mm"
include "chjoi.mm"
include "oveq2i.mm"
include "3eqtr4i.mm"

theorem qlax4i
  let cA: class A
  let cB: class B
  assume qlax.1: |- A e. CH
  assume qlax.2: |- B e. CH


  assert |- ( A vH ( B vH ( _|_ ` B ) ) ) = ( B vH ( _|_ ` B ) )

  proof
    cA
    chil
    chj
    co
    chil
    cA
    cB
    cB
    cort
    cfv
    chj
    co
    #
    chj
    co
    @0
    cA
    qlax.1
    chj1i
    @0
    chil
    cA
    chj
    cB
    qlax.2
    chjoi
    #
    oveq2i
    @1
    3eqtr4i
end
