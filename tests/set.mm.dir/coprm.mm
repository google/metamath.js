include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "prmz.mm"
include "gcddvds.mm"
include "sylan.mm"
include "simprd.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "con3d.mm"
include "wo.mm"
include "cn.mm"
include "cc0.mm"
include "0nnn.mm"
include "prmnn.mm"
include "eleq1.mm"
include "mtoi.mm"
include "intnanrd.mm"
include "adantr.mm"
include "wi.mm"
include "gcdn0cl.mm"
include "ex.mm"
include "mpd.mm"
include "simpld.mm"
include "cv.mm"
include "wral.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "isprm2.mm"
include "simprbi.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl5com.mm"
include "mp2d.mm"
include "biorf.mm"
include "orcom.mm"
include "syl6bb.mm"
include "syl5ibrcom.mm"
include "syld.mm"
include "cle.mm"
include "clt.mm"
include "wne.mm"
include "iddvds.mm"
include "syl.mm"
include "w3a.mm"
include "dvdslegcd.mm"
include "3anidm12.mm"
include "mpand.mm"
include "prmgt1.mm"
include "cr.mm"
include "zred.mm"
include "nnred.mm"
include "1re.mm"
include "ltletr.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "ltne.mm"
include "mpan.mm"
include "a1i.mm"
include "3syld.mm"
include "necon2bd.mm"
include "impbid.mm"

theorem coprm
  let cP: class P
  let cN: class N
  let vz: setvar z


  assert |- ( ( P e. Prime /\ N e. ZZ ) -> ( -. P || N <-> ( P gcd N ) = 1 ) )

  proof
    cP
    cprime
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cP
    cN
    cdvds
    wbr
    #
    wn
    #
    cP
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    @2
    @4
    @5
    cP
    wceq
    #
    wn
    #
    @6
    @2
    @7
    @3
    @2
    @5
    cN
    cdvds
    wbr
    #
    @7
    @3
    @2
    @5
    cP
    cdvds
    wbr
    #
    @9
    @0
    cP
    cz
    wcel
    #
    @1
    @10
    @9
    wa
    cP
    prmz
    #
    cP
    cN
    gcddvds
    sylan
    #
    simprd
    @5
    cP
    cN
    cdvds
    breq1
    syl5ibcom
    con3d
    @2
    @6
    @8
    @6
    @7
    wo
    #
    @2
    @5
    cn
    wcel
    #
    @10
    @14
    @2
    cP
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wa
    wn
    #
    @15
    @0
    @18
    @1
    @0
    @16
    @17
    @0
    @16
    cc0
    cn
    wcel
    #
    0nnn
    @0
    cP
    cn
    wcel
    @16
    @19
    cP
    prmnn
    cP
    cc0
    cn
    eleq1
    syl5ibcom
    mtoi
    intnanrd
    adantr
    #
    @0
    @11
    @1
    @18
    @15
    wi
    @12
    @11
    @1
    wa
    @18
    @15
    cP
    cN
    gcdn0cl
    ex
    sylan
    mpd
    #
    @2
    @10
    @9
    @13
    simpld
    @0
    @15
    @10
    @14
    wi
    #
    wi
    @1
    @0
    vz
    cv
    #
    cP
    cdvds
    wbr
    #
    @23
    c1
    wceq
    #
    @23
    cP
    wceq
    #
    wo
    #
    wi
    #
    vz
    cn
    wral
    #
    @15
    @22
    @0
    cP
    c2
    cuz
    cfv
    wcel
    @29
    vz
    cP
    isprm2
    simprbi
    @28
    @22
    vz
    @5
    cn
    @23
    @5
    wceq
    #
    @24
    @10
    @27
    @14
    @23
    @5
    cP
    cdvds
    breq1
    @30
    @25
    @6
    @26
    @7
    @23
    @5
    c1
    eqeq1
    @23
    @5
    cP
    eqeq1
    orbi12d
    imbi12d
    rspcv
    syl5com
    adantr
    mp2d
    @8
    @6
    @7
    @6
    wo
    @14
    @7
    @6
    biorf
    @7
    @6
    orcom
    syl6bb
    syl5ibrcom
    syld
    @2
    @3
    @5
    c1
    @2
    @3
    cP
    @5
    cle
    wbr
    #
    c1
    @5
    clt
    wbr
    #
    @5
    c1
    wne
    #
    @2
    cP
    cP
    cdvds
    wbr
    #
    @3
    @31
    @0
    @34
    @1
    @0
    @11
    @34
    @12
    cP
    iddvds
    syl
    adantr
    @2
    @18
    @34
    @3
    wa
    @31
    wi
    #
    @20
    @0
    @11
    @1
    @18
    @35
    wi
    #
    @12
    @11
    @1
    @36
    @11
    @11
    @1
    w3a
    @18
    @35
    cP
    cP
    cN
    dvdslegcd
    ex
    3anidm12
    sylan
    mpd
    mpand
    @2
    c1
    cP
    clt
    wbr
    #
    @31
    @32
    @0
    @37
    @1
    cP
    prmgt1
    adantr
    @2
    cP
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @37
    @31
    wa
    @32
    wi
    #
    @0
    @38
    @1
    @0
    cP
    @12
    zred
    adantr
    @2
    @5
    @21
    nnred
    c1
    cr
    wcel
    #
    @38
    @39
    @40
    1re
    c1
    cP
    @5
    ltletr
    mp3an1
    syl2anc
    mpand
    @32
    @33
    wi
    @2
    @41
    @32
    @33
    1re
    c1
    @5
    ltne
    mpan
    a1i
    3syld
    necon2bd
    impbid
end
