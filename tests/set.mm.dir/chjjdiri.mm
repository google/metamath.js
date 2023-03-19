include "chj.mm"
include "co.mm"
include "chjidmi.mm"
include "oveq2i.mm"
include "chj4i.mm"
include "eqtr3i.mm"

theorem chjjdiri
  let cA: class A
  let cB: class B
  let cC: class C
  assume chj12.1: |- A e. CH
  assume chj12.2: |- B e. CH
  assume chj12.3: |- C e. CH


  assert |- ( ( A vH B ) vH C ) = ( ( A vH C ) vH ( B vH C ) )

  proof
    cA
    cB
    chj
    co
    #
    cC
    cC
    chj
    co
    #
    chj
    co
    @0
    cC
    chj
    co
    cA
    cC
    chj
    co
    cB
    cC
    chj
    co
    chj
    co
    @1
    cC
    @0
    chj
    cC
    chj12.3
    chjidmi
    oveq2i
    cA
    cB
    cC
    cC
    chj12.1
    chj12.2
    chj12.3
    chj12.3
    chj4i
    eqtr3i
end
