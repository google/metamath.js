include "cin.mm"
include "chj.mm"
include "co.mm"
include "wss.mm"
include "inss1.mm"
include "chincli.mm"
include "chlubii.mm"
include "mp2an.mm"
include "inss2.mm"
include "chlej12i.mm"
include "ssini.mm"

theorem ledii
  let cA: class A
  let cB: class B
  let cC: class C
  assume ledi.1: |- A e. CH
  assume ledi.2: |- B e. CH
  assume ledi.3: |- C e. CH


  assert |- ( ( A i^i B ) vH ( A i^i C ) ) C_ ( A i^i ( B vH C ) )

  proof
    cA
    cB
    cin
    #
    cA
    cC
    cin
    #
    chj
    co
    #
    cA
    cB
    cC
    chj
    co
    #
    @0
    cA
    wss
    @1
    cA
    wss
    @2
    cA
    wss
    cA
    cB
    inss1
    cA
    cC
    inss1
    @0
    @1
    cA
    cA
    cB
    ledi.1
    ledi.2
    chincli
    #
    cA
    cC
    ledi.1
    ledi.3
    chincli
    #
    ledi.1
    chlubii
    mp2an
    @0
    cB
    wss
    @1
    cC
    wss
    @2
    @3
    wss
    cA
    cB
    inss2
    cA
    cC
    inss2
    @0
    cB
    @1
    cC
    @4
    ledi.2
    @5
    ledi.3
    chlej12i
    mp2an
    ssini
end
