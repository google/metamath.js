include "c2.mm"
include "wceq.mm"
include "codd.mm"
include "wcel.mm"
include "cprime.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "w3a.mm"
include "wo.mm"
include "wi.mm"
include "wn.mm"
include "eleq1.mm"
include "ceven.mm"
include "evennodd.mm"
include "pm2.21d.mm"
include "wne.mm"
include "df-ne.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "oddprmALTV.mm"
include "sylbir.mm"
include "ex.mm"
include "syl5bir.mm"
include "im2anan9.mm"
include "imp.mm"
include "opoeALTV.mm"
include "syl.mm"
include "syl11.mm"
include "expd.mm"
include "syl6bi.mm"
include "3imp231.mm"
include "com12.mm"
include "orc.mm"
include "a1d.mm"
include "olc.mm"
include "pm2.61ii.mm"

theorem odd2prm2
  let cP: class P
  let cQ: class Q
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. Odd /\ ( P e. Prime /\ Q e. Prime ) /\ N = ( P + Q ) ) -> ( P = 2 \/ Q = 2 ) )

  proof
    cP
    c2
    wceq
    #
    cQ
    c2
    wceq
    #
    cN
    codd
    wcel
    #
    cP
    cprime
    wcel
    #
    cQ
    cprime
    wcel
    #
    wa
    #
    cN
    cP
    cQ
    caddc
    co
    #
    wceq
    #
    w3a
    #
    @0
    @1
    wo
    #
    wi
    #
    @0
    wn
    #
    @1
    wn
    #
    @10
    @8
    @11
    @12
    wa
    #
    @9
    @7
    @2
    @5
    @13
    @9
    wi
    #
    @7
    @2
    @6
    codd
    wcel
    #
    @5
    @14
    wi
    cN
    @6
    codd
    eleq1
    @15
    @5
    @13
    @9
    @6
    ceven
    wcel
    #
    @15
    @9
    @5
    @13
    wa
    #
    @16
    @15
    @9
    @6
    evennodd
    pm2.21d
    @17
    cP
    codd
    wcel
    #
    cQ
    codd
    wcel
    #
    wa
    #
    @16
    @5
    @13
    @20
    @3
    @11
    @18
    @4
    @12
    @19
    @11
    cP
    c2
    wne
    #
    @3
    @18
    cP
    c2
    df-ne
    @3
    @21
    @18
    @3
    @21
    wa
    cP
    cprime
    c2
    csn
    cdif
    #
    wcel
    @18
    cP
    cprime
    c2
    eldifsn
    cP
    oddprmALTV
    sylbir
    ex
    syl5bir
    @12
    cQ
    c2
    wne
    #
    @4
    @19
    cQ
    c2
    df-ne
    @4
    @23
    @19
    @4
    @23
    wa
    cQ
    @22
    wcel
    @19
    cQ
    cprime
    c2
    eldifsn
    cQ
    oddprmALTV
    sylbir
    ex
    syl5bir
    im2anan9
    imp
    cP
    cQ
    opoeALTV
    syl
    syl11
    expd
    syl6bi
    3imp231
    com12
    ex
    @0
    @9
    @8
    @0
    @1
    orc
    a1d
    @1
    @9
    @8
    @1
    @0
    olc
    a1d
    pm2.61ii
end
