include "ceven.mm"
include "wcel.mm"
include "cprime.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "c2.mm"
include "wo.mm"
include "w3o.mm"
include "wi.mm"
include "olc.mm"
include "a1d.mm"
include "wn.mm"
include "wa.mm"
include "cmin.mm"
include "codd.mm"
include "wne.mm"
include "df-ne.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "oddprmALTV.mm"
include "emoo.mm"
include "expcom.mm"
include "syl.mm"
include "sylbir.mm"
include "ex.mm"
include "syl5bir.mm"
include "com23.mm"
include "3ad2ant3.mm"
include "impcom.mm"
include "3adant3.mm"
include "3simpa.mm"
include "3ad2ant2.mm"
include "adantl.mm"
include "eqcom.mm"
include "cc.mm"
include "evenz.mm"
include "zcnd.mm"
include "adantr.mm"
include "prmz.mm"
include "cz.mm"
include "zaddcl.mm"
include "syl2an.mm"
include "subadd2d.mm"
include "biimprd.mm"
include "syl5bi.mm"
include "3impia.mm"
include "odd2prm2.mm"
include "syl3anc.mm"
include "orcd.mm"
include "pm2.61i.mm"
include "df-3or.mm"
include "sylibr.mm"

theorem even3prm2
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. Even /\ ( P e. Prime /\ Q e. Prime /\ R e. Prime ) /\ N = ( ( P + Q ) + R ) ) -> ( P = 2 \/ Q = 2 \/ R = 2 ) )

  proof
    cN
    ceven
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
    cR
    cprime
    wcel
    #
    w3a
    #
    cN
    cP
    cQ
    caddc
    co
    #
    cR
    caddc
    co
    #
    wceq
    #
    w3a
    #
    cP
    c2
    wceq
    #
    cQ
    c2
    wceq
    #
    wo
    #
    cR
    c2
    wceq
    #
    wo
    #
    @9
    @10
    @12
    w3o
    @12
    @8
    @13
    wi
    @12
    @13
    @8
    @12
    @11
    olc
    a1d
    @12
    wn
    #
    @8
    @13
    @14
    @8
    wa
    #
    @11
    @12
    @15
    cN
    cR
    cmin
    co
    #
    codd
    wcel
    #
    @1
    @2
    wa
    #
    @16
    @5
    wceq
    #
    @11
    @8
    @14
    @17
    @0
    @4
    @14
    @17
    wi
    #
    @7
    @4
    @0
    @20
    @3
    @1
    @0
    @20
    wi
    @2
    @3
    @14
    @0
    @17
    @14
    cR
    c2
    wne
    #
    @3
    @0
    @17
    wi
    #
    cR
    c2
    df-ne
    @3
    @21
    @22
    @3
    @21
    wa
    cR
    cprime
    c2
    csn
    cdif
    wcel
    #
    @22
    cR
    cprime
    c2
    eldifsn
    @23
    cR
    codd
    wcel
    #
    @22
    cR
    oddprmALTV
    @0
    @24
    @17
    cN
    cR
    emoo
    expcom
    syl
    sylbir
    ex
    syl5bir
    com23
    3ad2ant3
    impcom
    3adant3
    impcom
    @8
    @18
    @14
    @4
    @0
    @18
    @7
    @1
    @2
    @3
    3simpa
    3ad2ant2
    adantl
    @8
    @19
    @14
    @0
    @4
    @7
    @19
    @7
    @6
    cN
    wceq
    #
    @0
    @4
    wa
    #
    @19
    cN
    @6
    eqcom
    @26
    @19
    @25
    @26
    cN
    cR
    @5
    @0
    cN
    cc
    wcel
    @4
    @0
    cN
    cN
    evenz
    zcnd
    adantr
    @4
    cR
    cc
    wcel
    #
    @0
    @3
    @1
    @27
    @2
    @3
    cR
    cR
    prmz
    zcnd
    3ad2ant3
    adantl
    @4
    @5
    cc
    wcel
    #
    @0
    @1
    @2
    @28
    @3
    @18
    @5
    @1
    cP
    cz
    wcel
    cQ
    cz
    wcel
    @5
    cz
    wcel
    @2
    cP
    prmz
    cQ
    prmz
    cP
    cQ
    zaddcl
    syl2an
    zcnd
    3adant3
    adantl
    subadd2d
    biimprd
    syl5bi
    3impia
    adantl
    cP
    cQ
    @16
    odd2prm2
    syl3anc
    orcd
    ex
    pm2.61i
    @9
    @10
    @12
    df-3or
    sylibr
end
