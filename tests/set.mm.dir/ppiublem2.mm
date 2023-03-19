include "cprime.mm"
include "wcel.mm"
include "c4.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c6.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "c5.mm"
include "cfz.mm"
include "c1.mm"
include "cpr.mm"
include "cmin.mm"
include "cz.mm"
include "cn.mm"
include "prmz.mm"
include "adantr.mm"
include "6nn.mm"
include "zmodfz.mm"
include "sylancl.mm"
include "caddc.mm"
include "df-6.mm"
include "oveq1i.mm"
include "5cn.mm"
include "ax-1cn.mm"
include "pncan3oi.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "syl6eleq.mm"
include "wi.mm"
include "c2.mm"
include "c3.mm"
include "6re.mm"
include "leidi.mm"
include "c0.mm"
include "noel.mm"
include "pm2.21i.mm"
include "clt.mm"
include "wceq.mm"
include "5lt6.mm"
include "wb.mm"
include "nnzi.mm"
include "5nn.mm"
include "fzn.mm"
include "mp2an.mm"
include "mpbi.mm"
include "eleq2s.mm"
include "a1i.mm"
include "pm3.2i.mm"
include "5nn0.mm"
include "cdvds.mm"
include "elexi.mm"
include "prid2.mm"
include "3mix3i.mm"
include "ppiublem1.mm"
include "4nn0.mm"
include "df-5.mm"
include "cmul.mm"
include "2z.mm"
include "dvdsmul1.mm"
include "2t2e4.mm"
include "breqtri.mm"
include "3mix1i.mm"
include "3nn0.mm"
include "df-4.mm"
include "3z.mm"
include "iddvds.mm"
include "ax-mp.mm"
include "3mix2i.mm"
include "2nn0.mm"
include "df-3.mm"
include "1nn0.mm"
include "df-2.mm"
include "1ex.mm"
include "prid1.mm"
include "0nn0.mm"
include "1e0p1.mm"
include "dvds0.mm"
include "simpri.mm"
include "mpd.mm"

theorem ppiublem2
  let cP: class P


  assert |- ( ( P e. Prime /\ 4 <_ P ) -> ( P mod 6 ) e. { 1 , 5 } )

  proof
    cP
    cprime
    wcel
    #
    c4
    cP
    cle
    wbr
    #
    wa
    #
    cP
    c6
    cmo
    co
    #
    cc0
    c5
    cfz
    co
    #
    wcel
    #
    @3
    c1
    c5
    cpr
    #
    wcel
    #
    @2
    @3
    cc0
    c6
    c1
    cmin
    co
    #
    cfz
    co
    #
    @4
    @2
    cP
    cz
    wcel
    #
    c6
    cn
    wcel
    @3
    @9
    wcel
    @0
    @10
    @1
    cP
    prmz
    adantr
    6nn
    cP
    c6
    zmodfz
    sylancl
    @8
    c5
    cc0
    cfz
    @8
    c5
    c1
    caddc
    co
    #
    c1
    cmin
    co
    c5
    c6
    @11
    c1
    cmin
    df-6
    oveq1i
    c5
    c1
    5cn
    ax-1cn
    pncan3oi
    eqtri
    oveq2i
    syl6eleq
    cc0
    c6
    cle
    wbr
    @2
    @5
    @7
    wi
    wi
    cP
    cc0
    c1
    cP
    c1
    c2
    cP
    c2
    c3
    cP
    c3
    c4
    cP
    c4
    c5
    cP
    c5
    c6
    c6
    c6
    cle
    wbr
    @2
    @3
    c6
    c5
    cfz
    co
    #
    wcel
    @7
    wi
    #
    wi
    c6
    6re
    leidi
    @13
    @2
    @7
    @3
    c0
    @12
    @3
    c0
    wcel
    @7
    @3
    noel
    pm2.21i
    c5
    c6
    clt
    wbr
    #
    @12
    c0
    wceq
    #
    5lt6
    c6
    cz
    wcel
    c5
    cz
    wcel
    @14
    @15
    wb
    c6
    6nn
    nnzi
    c5
    5nn
    nnzi
    c6
    c5
    fzn
    mp2an
    mpbi
    eleq2s
    a1i
    pm3.2i
    5nn0
    df-6
    c5
    @6
    wcel
    c2
    c5
    cdvds
    wbr
    c3
    c5
    cdvds
    wbr
    c1
    c5
    c5
    cn
    5nn
    elexi
    prid2
    3mix3i
    ppiublem1
    4nn0
    df-5
    c2
    c4
    cdvds
    wbr
    c3
    c4
    cdvds
    wbr
    c4
    @6
    wcel
    c2
    c2
    c2
    cmul
    co
    #
    c4
    cdvds
    c2
    cz
    wcel
    #
    @17
    c2
    @16
    cdvds
    wbr
    2z
    2z
    c2
    c2
    dvdsmul1
    mp2an
    2t2e4
    breqtri
    3mix1i
    ppiublem1
    3nn0
    df-4
    c3
    c3
    cdvds
    wbr
    #
    c2
    c3
    cdvds
    wbr
    c3
    @6
    wcel
    c3
    cz
    wcel
    @18
    3z
    c3
    iddvds
    ax-mp
    3mix2i
    ppiublem1
    2nn0
    df-3
    c2
    c2
    cdvds
    wbr
    #
    c3
    c2
    cdvds
    wbr
    c2
    @6
    wcel
    @17
    @19
    2z
    c2
    iddvds
    ax-mp
    3mix1i
    ppiublem1
    1nn0
    df-2
    c1
    @6
    wcel
    c2
    c1
    cdvds
    wbr
    c3
    c1
    cdvds
    wbr
    c1
    c5
    1ex
    prid1
    3mix3i
    ppiublem1
    0nn0
    1e0p1
    c2
    cc0
    cdvds
    wbr
    #
    c3
    cc0
    cdvds
    wbr
    cc0
    @6
    wcel
    @17
    @20
    2z
    c2
    dvds0
    ax-mp
    3mix1i
    ppiublem1
    simpri
    mpd
end
