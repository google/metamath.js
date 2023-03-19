include "wpo.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "poirr.mm"
include "adantrr.mm"
include "wi.mm"
include "potr.mm"
include "3exp2.mm"
include "com34.mm"
include "pm2.43d.mm"
include "imp32.mm"
include "mtod.mm"

theorem po2nr
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R


  assert |- ( ( R Po A /\ ( B e. A /\ C e. A ) ) -> -. ( B R C /\ C R B ) )

  proof
    cA
    cR
    wpo
    #
    cB
    cA
    wcel
    #
    cC
    cA
    wcel
    #
    wa
    wa
    cB
    cC
    cR
    wbr
    cC
    cB
    cR
    wbr
    wa
    #
    cB
    cB
    cR
    wbr
    #
    @0
    @1
    @4
    wn
    @2
    cA
    cB
    cR
    poirr
    adantrr
    @0
    @1
    @2
    @3
    @4
    wi
    #
    @0
    @1
    @2
    @5
    wi
    @0
    @1
    @2
    @1
    @5
    @0
    @1
    @2
    @1
    @5
    cA
    cB
    cC
    cB
    cR
    potr
    3exp2
    com34
    pm2.43d
    imp32
    mtod
end
