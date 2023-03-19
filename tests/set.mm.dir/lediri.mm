include "cin.mm"
include "chj.mm"
include "co.mm"
include "ledii.mm"
include "incom.mm"
include "oveq12i.mm"
include "3sstr4i.mm"

theorem lediri
  let cA: class A
  let cB: class B
  let cC: class C
  assume ledi.1: |- A e. CH
  assume ledi.2: |- B e. CH
  assume ledi.3: |- C e. CH


  assert |- ( ( A i^i C ) vH ( B i^i C ) ) C_ ( ( A vH B ) i^i C )

  proof
    cC
    cA
    cin
    #
    cC
    cB
    cin
    #
    chj
    co
    cC
    cA
    cB
    chj
    co
    #
    cin
    cA
    cC
    cin
    #
    cB
    cC
    cin
    #
    chj
    co
    @2
    cC
    cin
    cC
    cA
    cB
    ledi.3
    ledi.1
    ledi.2
    ledii
    @3
    @0
    @4
    @1
    chj
    cA
    cC
    incom
    cB
    cC
    incom
    oveq12i
    @2
    cC
    incom
    3sstr4i
end
