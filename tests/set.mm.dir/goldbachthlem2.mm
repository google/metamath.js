include "cn0.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cfmtno.mm"
include "cfv.mm"
include "cgcd.mm"
include "co.mm"
include "cdvds.mm"
include "wa.mm"
include "c1.mm"
include "wceq.mm"
include "cz.mm"
include "fmtnonn.mm"
include "nnzd.mm"
include "anim12ci.mm"
include "3adant3.mm"
include "gcddvds.mm"
include "syl.mm"
include "c2.mm"
include "cmin.mm"
include "goldbachthlem1.mm"
include "wi.mm"
include "gcdcl.mm"
include "nn0zd.mm"
include "3ad2ant2.mm"
include "2z.mm"
include "a1i.mm"
include "zsubcld.mm"
include "3ad2ant1.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "dvds2sub.mm"
include "ancomsd.mm"
include "cc.mm"
include "nncnd.mm"
include "2cnd.mm"
include "nncand.mm"
include "breq2d.mm"
include "wo.mm"
include "cprime.mm"
include "cn.mm"
include "wb.mm"
include "2prm.mm"
include "gcdnncl.mm"
include "dvdsprime.mm"
include "sylancr.mm"
include "breq1.mm"
include "adantl.mm"
include "fmtnoodd.mm"
include "pm2.21d.mm"
include "ad2antrr.mm"
include "sylbid.mm"
include "ex.mm"
include "com23.mm"
include "adantld.mm"
include "mpd.mm"
include "gcdcom.mm"
include "eqeq1d.mm"
include "biimpd.mm"
include "jaod.mm"
include "syld.mm"
include "syland.mm"

theorem goldbachthlem2
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN0 /\ M e. NN0 /\ M < N ) -> ( ( FermatNo ` N ) gcd ( FermatNo ` M ) ) = 1 )

  proof
    cN
    cn0
    wcel
    #
    cM
    cn0
    wcel
    #
    cM
    cN
    clt
    wbr
    #
    w3a
    #
    cM
    cfmtno
    cfv
    #
    cN
    cfmtno
    cfv
    #
    cgcd
    co
    #
    @4
    cdvds
    wbr
    #
    @6
    @5
    cdvds
    wbr
    #
    wa
    #
    @5
    @4
    cgcd
    co
    #
    c1
    wceq
    #
    @3
    @4
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    wa
    #
    @9
    @0
    @1
    @14
    @2
    @0
    @13
    @1
    @12
    @0
    @5
    cN
    fmtnonn
    #
    nnzd
    #
    @1
    @4
    cM
    fmtnonn
    #
    nnzd
    #
    anim12ci
    #
    3adant3
    #
    @4
    @5
    gcddvds
    #
    syl
    @3
    @7
    @6
    @5
    c2
    cmin
    co
    #
    cdvds
    wbr
    #
    @8
    @11
    @3
    @7
    @4
    @22
    cdvds
    wbr
    #
    @23
    cM
    cN
    goldbachthlem1
    @3
    @6
    cz
    wcel
    #
    @12
    @22
    cz
    wcel
    #
    @7
    @24
    wa
    @23
    wi
    @3
    @6
    @3
    @14
    @6
    cn0
    wcel
    @20
    @4
    @5
    gcdcl
    syl
    nn0zd
    #
    @1
    @0
    @12
    @2
    @18
    3ad2ant2
    @0
    @1
    @26
    @2
    @0
    @5
    c2
    @16
    c2
    cz
    wcel
    @0
    2z
    a1i
    zsubcld
    3ad2ant1
    #
    @6
    @4
    @22
    dvdstr
    syl3anc
    mpan2d
    @3
    @23
    @8
    wa
    @6
    @5
    @22
    cmin
    co
    #
    cdvds
    wbr
    #
    @11
    @3
    @8
    @23
    @30
    @3
    @25
    @13
    @26
    @8
    @23
    wa
    @30
    wi
    @27
    @0
    @1
    @13
    @2
    @16
    3ad2ant1
    @28
    @6
    @5
    @22
    dvds2sub
    syl3anc
    ancomsd
    @3
    @30
    @6
    c2
    cdvds
    wbr
    #
    @11
    @3
    @29
    c2
    @6
    cdvds
    @3
    @5
    c2
    @0
    @1
    @5
    cc
    wcel
    @2
    @0
    @5
    @15
    nncnd
    3ad2ant1
    @3
    2cnd
    nncand
    breq2d
    @3
    @31
    @6
    c2
    wceq
    #
    @6
    c1
    wceq
    #
    wo
    #
    @11
    @3
    c2
    cprime
    wcel
    @6
    cn
    wcel
    #
    @31
    @34
    wb
    2prm
    @3
    @4
    cn
    wcel
    #
    @5
    cn
    wcel
    #
    wa
    #
    @35
    @0
    @1
    @38
    @2
    @0
    @37
    @1
    @36
    @15
    @17
    anim12ci
    3adant3
    @4
    @5
    gcdnncl
    syl
    c2
    @6
    dvdsprime
    sylancr
    @3
    @32
    @11
    @33
    @0
    @1
    @32
    @11
    wi
    #
    @2
    @0
    @1
    wa
    #
    @9
    @39
    @40
    @14
    @9
    @19
    @21
    syl
    @40
    @8
    @39
    @7
    @40
    @32
    @8
    @11
    @40
    @32
    @8
    @11
    wi
    @40
    @32
    wa
    @8
    c2
    @5
    cdvds
    wbr
    #
    @11
    @32
    @8
    @41
    wb
    @40
    @6
    c2
    @5
    cdvds
    breq1
    adantl
    @0
    @41
    @11
    wi
    @1
    @32
    @0
    @41
    @11
    cN
    fmtnoodd
    pm2.21d
    ad2antrr
    sylbid
    ex
    com23
    adantld
    mpd
    3adant3
    @3
    @33
    @11
    @3
    @6
    @10
    c1
    @3
    @14
    @6
    @10
    wceq
    @20
    @4
    @5
    gcdcom
    syl
    eqeq1d
    biimpd
    jaod
    sylbid
    sylbid
    syld
    syland
    mpd
end
