include "chj.mm"
include "co.mm"
include "chjcomi.mm"
include "oveq1i.mm"
include "chjassi.mm"
include "3eqtr3i.mm"

theorem chj12i
  let cA: class A
  let cB: class B
  let cC: class C
  assume chj12.1: |- A e. CH
  assume chj12.2: |- B e. CH
  assume chj12.3: |- C e. CH


  assert |- ( A vH ( B vH C ) ) = ( B vH ( A vH C ) )

  proof
    cA
    cB
    chj
    co
    #
    cC
    chj
    co
    cB
    cA
    chj
    co
    #
    cC
    chj
    co
    cA
    cB
    cC
    chj
    co
    chj
    co
    cB
    cA
    cC
    chj
    co
    chj
    co
    @0
    @1
    cC
    chj
    cA
    cB
    chj12.1
    chj12.2
    chjcomi
    oveq1i
    cA
    cB
    cC
    chj12.1
    chj12.2
    chj12.3
    chjassi
    cB
    cA
    cC
    chj12.2
    chj12.1
    chj12.3
    chjassi
    3eqtr3i
end
