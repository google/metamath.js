include "cprime.mm"
include "wcel.mm"
include "wa.mm"
include "codd.mm"
include "ceven.mm"
include "c4.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "wi.mm"
include "wn.mm"
include "c2.mm"
include "wb.mm"
include "cn.mm"
include "prmnn.mm"
include "nneoALTV.mm"
include "bicomd.mm"
include "syl.mm"
include "evenprm2.mm"
include "bitrd.mm"
include "adantl.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "3anbi3d.mm"
include "breq2.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "cz.mm"
include "prmz.mm"
include "2evenALTV.mm"
include "evensumeven.mm"
include "sylancl.mm"
include "oveq1.mm"
include "2p2e4.mm"
include "syl6eq.mm"
include "breq2d.mm"
include "4re.mm"
include "ltnri.mm"
include "pm2.21i.mm"
include "syl6bi.mm"
include "sylbird.mm"
include "com13.mm"
include "imp.mm"
include "expd.mm"
include "3imp.mm"
include "com12.mm"
include "adantr.mm"
include "sylbid.mm"
include "ex.mm"
include "ax-1.mm"
include "pm2.61d2.mm"

theorem sbgoldbaltlem1
  let cP: class P
  let cQ: class Q
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( P e. Prime /\ Q e. Prime ) -> ( ( N e. Even /\ 4 < N /\ N = ( P + Q ) ) -> Q e. Odd ) )

  proof
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
    cQ
    codd
    wcel
    #
    cN
    ceven
    wcel
    #
    c4
    cN
    clt
    wbr
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
    @3
    wi
    #
    @2
    @3
    wn
    #
    cQ
    c2
    wceq
    #
    @9
    @1
    @10
    @11
    wb
    @0
    @1
    @10
    cQ
    ceven
    wcel
    #
    @11
    @1
    cQ
    cn
    wcel
    #
    @10
    @12
    wb
    cQ
    prmnn
    @13
    @12
    @10
    cQ
    nneoALTV
    bicomd
    syl
    cQ
    evenprm2
    bitrd
    adantl
    @0
    @11
    @9
    wi
    @1
    @0
    @11
    @9
    @0
    @11
    wa
    #
    @8
    @4
    @5
    cN
    cP
    c2
    caddc
    co
    #
    wceq
    #
    w3a
    #
    @3
    @14
    @7
    @16
    @4
    @5
    @11
    @7
    @16
    wb
    @0
    @11
    @6
    @15
    cN
    cQ
    c2
    cP
    caddc
    oveq2
    eqeq2d
    adantl
    3anbi3d
    @0
    @17
    @3
    wi
    @11
    @17
    @0
    @3
    @4
    @5
    @16
    @0
    @3
    wi
    #
    @16
    @5
    @4
    @18
    @16
    @5
    @4
    @18
    @16
    @5
    @4
    wa
    c4
    @15
    clt
    wbr
    #
    @15
    ceven
    wcel
    #
    wa
    @18
    @16
    @5
    @19
    @4
    @20
    cN
    @15
    c4
    clt
    breq2
    cN
    @15
    ceven
    eleq1
    anbi12d
    @19
    @20
    @18
    @0
    @20
    @19
    @3
    @0
    @20
    cP
    ceven
    wcel
    #
    @19
    @3
    wi
    #
    @0
    cP
    cz
    wcel
    c2
    ceven
    wcel
    @21
    @20
    wb
    cP
    prmz
    2evenALTV
    cP
    c2
    evensumeven
    sylancl
    @0
    @21
    cP
    c2
    wceq
    #
    @22
    cP
    evenprm2
    @23
    @19
    c4
    c4
    clt
    wbr
    #
    @3
    @23
    @15
    c4
    c4
    clt
    @23
    @15
    c2
    c2
    caddc
    co
    c4
    cP
    c2
    c2
    caddc
    oveq1
    2p2e4
    syl6eq
    breq2d
    @24
    @3
    c4
    4re
    ltnri
    pm2.21i
    syl6bi
    syl6bi
    sylbird
    com13
    imp
    syl6bi
    expd
    com13
    3imp
    com12
    adantr
    sylbid
    ex
    adantr
    sylbid
    @3
    @8
    ax-1
    pm2.61d2
end
