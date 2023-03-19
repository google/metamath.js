include "cprime.mm"
include "wcel.mm"
include "c5.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cc0.mm"
include "c4.mm"
include "cfz.mm"
include "co.mm"
include "c2.mm"
include "wceq.mm"
include "c3.mm"
include "wo.mm"
include "cn0.mm"
include "cle.mm"
include "prmnn.mm"
include "nnnn0d.mm"
include "adantr.mm"
include "4nn0.mm"
include "a1i.mm"
include "c1.mm"
include "caddc.mm"
include "df-5.mm"
include "breq2i.mm"
include "cz.mm"
include "wb.mm"
include "prmz.mm"
include "4z.mm"
include "zleltp1.mm"
include "sylancl.mm"
include "biimprd.mm"
include "syl5bi.mm"
include "imp.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "ctp.mm"
include "cpr.mm"
include "cun.mm"
include "fz0to4untppr.mm"
include "eleq2i.mm"
include "wi.mm"
include "elun.mm"
include "w3o.mm"
include "eltpi.mm"
include "cn.mm"
include "wne.mm"
include "nnne0.mm"
include "eqneqall.mm"
include "com12.mm"
include "3syl.mm"
include "eleq1.mm"
include "1nprm.mm"
include "pm2.21i.mm"
include "syl6bi.mm"
include "orc.mm"
include "a1d.mm"
include "3jaoi.mm"
include "syl.mm"
include "elpri.mm"
include "olc.mm"
include "4nprm.mm"
include "jaoi.mm"
include "sylbi.mm"
include "mpd.mm"

theorem prm23lt5
  let cP: class P


  assert |- ( ( P e. Prime /\ P < 5 ) -> ( P = 2 \/ P = 3 ) )

  proof
    cP
    cprime
    wcel
    #
    cP
    c5
    clt
    wbr
    #
    wa
    #
    cP
    cc0
    c4
    cfz
    co
    #
    wcel
    #
    cP
    c2
    wceq
    #
    cP
    c3
    wceq
    #
    wo
    #
    @2
    cP
    cn0
    wcel
    #
    c4
    cn0
    wcel
    #
    cP
    c4
    cle
    wbr
    #
    @4
    @0
    @8
    @1
    @0
    cP
    cP
    prmnn
    #
    nnnn0d
    adantr
    @9
    @2
    4nn0
    a1i
    @0
    @1
    @10
    @1
    cP
    c4
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @0
    @10
    c5
    @12
    cP
    clt
    df-5
    breq2i
    @0
    @10
    @13
    @0
    cP
    cz
    wcel
    c4
    cz
    wcel
    @10
    @13
    wb
    cP
    prmz
    4z
    cP
    c4
    zleltp1
    sylancl
    biimprd
    syl5bi
    imp
    cP
    c4
    elfz2nn0
    syl3anbrc
    @4
    cP
    cc0
    c1
    c2
    ctp
    #
    c3
    c4
    cpr
    #
    cun
    #
    wcel
    #
    @2
    @7
    @3
    @16
    cP
    fz0to4untppr
    eleq2i
    @0
    @17
    @7
    wi
    @1
    @17
    @0
    @7
    @17
    cP
    @14
    wcel
    #
    cP
    @15
    wcel
    #
    wo
    @0
    @7
    wi
    #
    cP
    @14
    @15
    elun
    @18
    @20
    @19
    @18
    cP
    cc0
    wceq
    #
    cP
    c1
    wceq
    #
    @5
    w3o
    @20
    cP
    cc0
    c1
    c2
    eltpi
    @21
    @20
    @22
    @5
    @0
    @21
    @7
    @0
    cP
    cn
    wcel
    cP
    cc0
    wne
    #
    @21
    @7
    wi
    @11
    cP
    nnne0
    @21
    @23
    @7
    @7
    cP
    cc0
    eqneqall
    com12
    3syl
    com12
    @22
    @0
    c1
    cprime
    wcel
    #
    @7
    cP
    c1
    cprime
    eleq1
    @24
    @7
    1nprm
    pm2.21i
    syl6bi
    @5
    @7
    @0
    @5
    @6
    orc
    a1d
    3jaoi
    syl
    @19
    @6
    cP
    c4
    wceq
    #
    wo
    @20
    cP
    c3
    c4
    elpri
    @6
    @20
    @25
    @6
    @7
    @0
    @6
    @5
    olc
    a1d
    @25
    @0
    c4
    cprime
    wcel
    #
    @7
    cP
    c4
    cprime
    eleq1
    @26
    @7
    4nprm
    pm2.21i
    syl6bi
    jaoi
    syl
    jaoi
    sylbi
    com12
    adantr
    syl5bi
    mpd
end
