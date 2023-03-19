include "wss.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "ssid.mm"
include "chlubii.mm"
include "mpan2.mm"
include "chub2i.mm"
include "jctir.mm"
include "eqss.mm"
include "sylibr.mm"
include "chub1i.mm"
include "eqimss.mm"
include "syl5ss.mm"
include "impbii.mm"

theorem chlejb1i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( A C_ B <-> ( A vH B ) = B )

  proof
    cA
    cB
    wss
    #
    cA
    cB
    chj
    co
    #
    cB
    wceq
    #
    @0
    @1
    cB
    wss
    #
    cB
    @1
    wss
    #
    wa
    @2
    @0
    @3
    @4
    @0
    cB
    cB
    wss
    @3
    cB
    ssid
    cA
    cB
    cB
    ch0le.1
    chjcl.2
    chjcl.2
    chlubii
    mpan2
    cB
    cA
    chjcl.2
    ch0le.1
    chub2i
    jctir
    @1
    cB
    eqss
    sylibr
    @2
    cA
    @1
    cB
    cA
    cB
    ch0le.1
    chjcl.2
    chub1i
    @1
    cB
    eqimss
    syl5ss
    impbii
end
