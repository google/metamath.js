include "cin.mm"
include "chj.mm"
include "co.mm"
include "wss.mm"
include "chub1i.mm"
include "ssini.mm"
include "inss1.mm"
include "chub2i.mm"
include "sstri.mm"
include "inss2.mm"
include "wa.mm"
include "chincli.mm"
include "chjcli.mm"
include "chlubi.mm"
include "bicomi.mm"
include "mpbir2an.mm"

theorem lejdii
  let cA: class A
  let cB: class B
  let cC: class C
  assume ledi.1: |- A e. CH
  assume ledi.2: |- B e. CH
  assume ledi.3: |- C e. CH


  assert |- ( A vH ( B i^i C ) ) C_ ( ( A vH B ) i^i ( A vH C ) )

  proof
    cA
    cB
    cC
    cin
    #
    chj
    co
    cA
    cB
    chj
    co
    #
    cA
    cC
    chj
    co
    #
    cin
    #
    wss
    #
    cA
    @3
    wss
    #
    @0
    @3
    wss
    #
    cA
    @1
    @2
    cA
    cB
    ledi.1
    ledi.2
    chub1i
    cA
    cC
    ledi.1
    ledi.3
    chub1i
    ssini
    @0
    @1
    @2
    @0
    cB
    @1
    cB
    cC
    inss1
    cB
    cA
    ledi.2
    ledi.1
    chub2i
    sstri
    @0
    cC
    @2
    cB
    cC
    inss2
    cC
    cA
    ledi.3
    ledi.1
    chub2i
    sstri
    ssini
    @5
    @6
    wa
    @4
    cA
    @0
    @3
    ledi.1
    cB
    cC
    ledi.2
    ledi.3
    chincli
    @1
    @2
    cA
    cB
    ledi.1
    ledi.2
    chjcli
    cA
    cC
    ledi.1
    ledi.3
    chjcli
    chincli
    chlubi
    bicomi
    mpbir2an
end
