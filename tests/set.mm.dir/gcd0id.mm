include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "cgcd.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "gcd0val.mm"
include "oveq2.mm"
include "fveq2.mm"
include "abs0.mm"
include "syl6eq.mm"
include "3eqtr4a.mm"
include "adantl.mm"
include "wne.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cdvds.mm"
include "0z.mm"
include "gcddvds.mm"
include "mpan.mm"
include "simprd.mm"
include "adantr.mm"
include "wi.mm"
include "cn0.mm"
include "gcdcl.mm"
include "nn0zd.mm"
include "dvdsleabs.mm"
include "syl3an1.mm"
include "3anidm12.mm"
include "mpd.mm"
include "zabscl.mm"
include "dvds0.mm"
include "syl.mm"
include "iddvds.mm"
include "wb.mm"
include "absdvdsb.mm"
include "anidms.mm"
include "mpbid.mm"
include "jca.mm"
include "wn.mm"
include "eqid.mm"
include "biantrur.mm"
include "necon3abii.mm"
include "w3a.mm"
include "dvdslegcd.mm"
include "ex.mm"
include "mp3an2.mm"
include "mpancom.mm"
include "syl5bi.mm"
include "imp.mm"
include "zred.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "pm2.61dane.mm"

theorem gcd0id
  let cN: class N


  assert |- ( N e. ZZ -> ( 0 gcd N ) = ( abs ` N ) )

  proof
    cN
    cz
    wcel
    #
    cc0
    cN
    cgcd
    co
    #
    cN
    cabs
    cfv
    #
    wceq
    #
    cN
    cc0
    cN
    cc0
    wceq
    #
    @3
    @0
    @4
    cc0
    cc0
    cgcd
    co
    cc0
    @1
    @2
    gcd0val
    cN
    cc0
    cc0
    cgcd
    oveq2
    @4
    @2
    cc0
    cabs
    cfv
    cc0
    cN
    cc0
    cabs
    fveq2
    abs0
    syl6eq
    3eqtr4a
    adantl
    @0
    cN
    cc0
    wne
    #
    wa
    #
    @3
    @1
    @2
    cle
    wbr
    #
    @2
    @1
    cle
    wbr
    #
    @6
    @1
    cN
    cdvds
    wbr
    #
    @7
    @0
    @9
    @5
    @0
    @1
    cc0
    cdvds
    wbr
    #
    @9
    cc0
    cz
    wcel
    #
    @0
    @10
    @9
    wa
    0z
    cc0
    cN
    gcddvds
    mpan
    simprd
    adantr
    @0
    @5
    @9
    @7
    wi
    #
    @0
    @1
    cz
    wcel
    @0
    @5
    @12
    @0
    @1
    @11
    @0
    @1
    cn0
    wcel
    0z
    cc0
    cN
    gcdcl
    mpan
    nn0zd
    #
    @1
    cN
    dvdsleabs
    syl3an1
    3anidm12
    mpd
    @6
    @2
    cc0
    cdvds
    wbr
    #
    @2
    cN
    cdvds
    wbr
    #
    wa
    #
    @8
    @0
    @16
    @5
    @0
    @14
    @15
    @0
    @2
    cz
    wcel
    #
    @14
    cN
    zabscl
    #
    @2
    dvds0
    syl
    @0
    cN
    cN
    cdvds
    wbr
    #
    @15
    cN
    iddvds
    @0
    @19
    @15
    wb
    cN
    cN
    absdvdsb
    anidms
    mpbid
    jca
    adantr
    @0
    @5
    @16
    @8
    wi
    #
    @5
    cc0
    cc0
    wceq
    #
    @4
    wa
    #
    wn
    #
    @0
    @20
    @22
    cN
    cc0
    @21
    @4
    cc0
    eqid
    biantrur
    necon3abii
    @17
    @0
    @23
    @20
    wi
    #
    @18
    @17
    @11
    @0
    @24
    0z
    @17
    @11
    @0
    w3a
    @23
    @20
    @2
    cc0
    cN
    dvdslegcd
    ex
    mp3an2
    mpancom
    syl5bi
    imp
    mpd
    @0
    @3
    @7
    @8
    wa
    wb
    @5
    @0
    @1
    @2
    @0
    @1
    @13
    zred
    @0
    @2
    @18
    zred
    letri3d
    adantr
    mpbir2and
    pm2.61dane
end
