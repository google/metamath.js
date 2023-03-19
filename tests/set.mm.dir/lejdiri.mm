include "cin.mm"
include "chj.mm"
include "co.mm"
include "lejdii.mm"
include "chincli.mm"
include "chjcomi.mm"
include "ineq12i.mm"
include "3sstr4i.mm"

theorem lejdiri
  let cA: class A
  let cB: class B
  let cC: class C
  assume ledi.1: |- A e. CH
  assume ledi.2: |- B e. CH
  assume ledi.3: |- C e. CH


  assert |- ( ( A i^i B ) vH C ) C_ ( ( A vH C ) i^i ( B vH C ) )

  proof
    cC
    cA
    cB
    cin
    #
    chj
    co
    cC
    cA
    chj
    co
    #
    cC
    cB
    chj
    co
    #
    cin
    @0
    cC
    chj
    co
    cA
    cC
    chj
    co
    #
    cB
    cC
    chj
    co
    #
    cin
    cC
    cA
    cB
    ledi.3
    ledi.1
    ledi.2
    lejdii
    @0
    cC
    cA
    cB
    ledi.1
    ledi.2
    chincli
    ledi.3
    chjcomi
    @3
    @1
    @4
    @2
    cA
    cC
    ledi.1
    ledi.3
    chjcomi
    cB
    cC
    ledi.2
    ledi.3
    chjcomi
    ineq12i
    3sstr4i
end
