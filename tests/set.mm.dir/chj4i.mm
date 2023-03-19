include "chj.mm"
include "co.mm"
include "chj12i.mm"
include "oveq2i.mm"
include "chjcli.mm"
include "chjassi.mm"
include "3eqtr4i.mm"

theorem chj4i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume chj12.1: |- A e. CH
  assume chj12.2: |- B e. CH
  assume chj12.3: |- C e. CH
  assume chj4.4: |- D e. CH


  assert |- ( ( A vH B ) vH ( C vH D ) ) = ( ( A vH C ) vH ( B vH D ) )

  proof
    cA
    cB
    cC
    cD
    chj
    co
    #
    chj
    co
    #
    chj
    co
    cA
    cC
    cB
    cD
    chj
    co
    #
    chj
    co
    #
    chj
    co
    cA
    cB
    chj
    co
    @0
    chj
    co
    cA
    cC
    chj
    co
    @2
    chj
    co
    @1
    @3
    cA
    chj
    cB
    cC
    cD
    chj12.2
    chj12.3
    chj4.4
    chj12i
    oveq2i
    cA
    cB
    @0
    chj12.1
    chj12.2
    cC
    cD
    chj12.3
    chj4.4
    chjcli
    chjassi
    cA
    cC
    @2
    chj12.1
    chj12.3
    cB
    cD
    chj12.2
    chj4.4
    chjcli
    chjassi
    3eqtr4i
end
