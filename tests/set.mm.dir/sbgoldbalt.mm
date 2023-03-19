include "c4.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cgbe.mm"
include "wcel.mm"
include "wi.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cprime.mm"
include "wrex.mm"
include "ceven.mm"
include "c1.mm"
include "cle.mm"
include "cz.mm"
include "wb.mm"
include "2z.mm"
include "evenz.mm"
include "zltp1le.mm"
include "sylancr.mm"
include "c3.mm"
include "2p1e3.mm"
include "breq1i.mm"
include "wo.mm"
include "cr.mm"
include "3re.mm"
include "a1i.mm"
include "zred.mm"
include "leloed.mm"
include "3z.mm"
include "3p1e4.mm"
include "4re.mm"
include "wa.mm"
include "pm3.35.mm"
include "codd.mm"
include "w3a.mm"
include "isgbe.mm"
include "simp3.mm"
include "reximdva.mm"
include "imp.mm"
include "sylbi.mm"
include "a1d.mm"
include "syl.mm"
include "ex.mm"
include "com23.mm"
include "2prm.mm"
include "2p2e4.mm"
include "eqcomi.mm"
include "rspceov.mm"
include "mp3an.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "mpbii.mm"
include "jaoi.mm"
include "com12.mm"
include "sylbid.mm"
include "syl5bi.mm"
include "wn.mm"
include "3odd.mm"
include "eleq1.mm"
include "oddneven.mm"
include "pm2.21d.mm"
include "2lt4.mm"
include "2re.mm"
include "lttr.mm"
include "syl3anc.mm"
include "mpani.mm"
include "simpll.mm"
include "simpr.mm"
include "anim1i.mm"
include "adantr.mm"
include "df-3an.mm"
include "sylibr.mm"
include "sbgoldbaltlem2.mm"
include "sylc.mm"
include "sylanbrc.mm"
include "jca.mm"
include "syl6ibr.mm"
include "embantd.mm"
include "impbid.mm"
include "ralbiia.mm"

theorem sbgoldbalt
  let vn: setvar n
  let vq: setvar q
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x

  disjoint n p
  disjoint n q
  disjoint p q
  disjoint k x
  assert |- ( A. n e. Even ( 4 < n -> n e. GoldbachEven ) <-> A. n e. Even ( 2 < n -> E. p e. Prime E. q e. Prime n = ( p + q ) ) )

  proof
    c4
    vn
    cv
    #
    clt
    wbr
    #
    @0
    cgbe
    wcel
    #
    wi
    #
    c2
    @0
    clt
    wbr
    #
    @0
    vp
    cv
    #
    vq
    cv
    #
    caddc
    co
    #
    wceq
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    #
    wi
    #
    vn
    ceven
    @0
    ceven
    wcel
    #
    @3
    @11
    @12
    @4
    @3
    @10
    @12
    @4
    c2
    c1
    caddc
    co
    #
    @0
    cle
    wbr
    #
    @3
    @10
    wi
    #
    @12
    c2
    cz
    wcel
    @0
    cz
    wcel
    #
    @4
    @14
    wb
    2z
    @0
    evenz
    #
    c2
    @0
    zltp1le
    sylancr
    @14
    c3
    @0
    cle
    wbr
    #
    @12
    @15
    @13
    c3
    @0
    cle
    2p1e3
    breq1i
    @12
    @18
    c3
    @0
    clt
    wbr
    #
    c3
    @0
    wceq
    #
    wo
    #
    @15
    @12
    c3
    @0
    c3
    cr
    wcel
    @12
    3re
    a1i
    @12
    @0
    @17
    zred
    #
    leloed
    @21
    @12
    @15
    @19
    @12
    @15
    wi
    #
    @20
    @12
    @19
    @15
    @12
    @19
    c3
    c1
    caddc
    co
    #
    @0
    cle
    wbr
    #
    @15
    @12
    c3
    cz
    wcel
    @16
    @19
    @25
    wb
    3z
    @17
    c3
    @0
    zltp1le
    sylancr
    @25
    c4
    @0
    cle
    wbr
    #
    @12
    @15
    @24
    c4
    @0
    cle
    3p1e4
    breq1i
    @12
    @26
    @1
    c4
    @0
    wceq
    #
    wo
    #
    @15
    @12
    c4
    @0
    c4
    cr
    wcel
    #
    @12
    4re
    a1i
    #
    @22
    leloed
    @28
    @12
    @15
    @1
    @23
    @27
    @1
    @3
    @12
    @10
    @1
    @3
    @12
    @10
    wi
    #
    @1
    @3
    wa
    @2
    @31
    @1
    @2
    pm3.35
    @2
    @10
    @12
    @2
    @12
    @5
    codd
    wcel
    #
    @6
    codd
    wcel
    #
    @8
    w3a
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    #
    wa
    #
    @10
    @0
    vq
    vp
    isgbe
    #
    @12
    @36
    @10
    @12
    @35
    @9
    vp
    cprime
    @12
    @5
    cprime
    wcel
    #
    wa
    #
    @34
    @8
    vq
    cprime
    @34
    @8
    wi
    @40
    @6
    cprime
    wcel
    #
    wa
    @32
    @33
    @8
    simp3
    a1i
    reximdva
    reximdva
    imp
    sylbi
    a1d
    syl
    ex
    com23
    @27
    @15
    @12
    @27
    @10
    @3
    @27
    c4
    @7
    wceq
    #
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    #
    @10
    c2
    cprime
    wcel
    #
    @44
    c4
    c2
    c2
    caddc
    co
    #
    wceq
    @43
    2prm
    2prm
    @45
    c4
    2p2e4
    eqcomi
    vp
    vq
    cprime
    cprime
    c2
    c2
    c4
    caddc
    rspceov
    mp3an
    @27
    @42
    @8
    vp
    vq
    cprime
    cprime
    c4
    @0
    @7
    eqeq1
    2rexbidv
    mpbii
    a1d
    a1d
    jaoi
    com12
    sylbid
    syl5bi
    sylbid
    com12
    @20
    @12
    @15
    @20
    @0
    codd
    wcel
    #
    @12
    wn
    @20
    c3
    codd
    wcel
    @46
    3odd
    c3
    @0
    codd
    eleq1
    mpbii
    @0
    oddneven
    syl
    pm2.21d
    jaoi
    com12
    sylbid
    syl5bi
    sylbid
    com23
    @12
    @1
    @11
    @2
    @12
    @1
    @11
    @2
    wi
    @12
    @1
    wa
    #
    @4
    @10
    @2
    @12
    @1
    @4
    @12
    c2
    c4
    clt
    wbr
    #
    @1
    @4
    2lt4
    @12
    c2
    cr
    wcel
    #
    @29
    @0
    cr
    wcel
    @48
    @1
    wa
    @4
    wi
    @49
    @12
    2re
    a1i
    @30
    @22
    c2
    c4
    @0
    lttr
    syl3anc
    mpani
    imp
    @47
    @10
    @37
    @2
    @47
    @10
    @37
    @47
    @10
    wa
    @12
    @36
    @12
    @1
    @10
    simpll
    @47
    @10
    @36
    @47
    @9
    @35
    vp
    cprime
    @47
    @39
    wa
    #
    @8
    @34
    vq
    cprime
    @50
    @41
    wa
    #
    @8
    @34
    @51
    @8
    wa
    #
    @32
    @33
    wa
    #
    @8
    @34
    @52
    @39
    @41
    wa
    #
    @12
    @1
    @8
    w3a
    #
    @53
    @51
    @54
    @8
    @50
    @39
    @41
    @47
    @39
    simpr
    anim1i
    adantr
    @52
    @47
    @8
    wa
    @55
    @51
    @47
    @8
    @47
    @39
    @41
    simpll
    anim1i
    @12
    @1
    @8
    df-3an
    sylibr
    @5
    @6
    @0
    sbgoldbaltlem2
    sylc
    @51
    @8
    simpr
    @32
    @33
    @8
    df-3an
    sylanbrc
    ex
    reximdva
    reximdva
    imp
    jca
    ex
    @38
    syl6ibr
    embantd
    ex
    com23
    impbid
    ralbiia
end
