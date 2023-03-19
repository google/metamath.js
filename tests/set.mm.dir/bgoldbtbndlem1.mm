include "codd.mm"
include "wcel.mm"
include "c7.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "c3.mm"
include "cdc.mm"
include "cico.mm"
include "co.mm"
include "cgbo.mm"
include "cxr.mm"
include "cle.mm"
include "w3a.mm"
include "wa.mm"
include "wb.mm"
include "7re.mm"
include "rexri.mm"
include "1nn0.mm"
include "3nn.mm"
include "decnncl.mm"
include "nnrei.mm"
include "elico1.mm"
include "mp2an.mm"
include "wi.mm"
include "c8.mm"
include "wceq.mm"
include "wo.mm"
include "cz.mm"
include "7nn.mm"
include "nnzi.mm"
include "oddz.mm"
include "caddc.mm"
include "zltp1le.mm"
include "7p1e8.mm"
include "breq1i.mm"
include "a1i.mm"
include "cr.mm"
include "8re.mm"
include "zre.mm"
include "leloe.mm"
include "syl2an.mm"
include "3bitrd.mm"
include "sylancr.mm"
include "c9.mm"
include "8nn.mm"
include "8p1e9.mm"
include "9re.mm"
include "zred.mm"
include "leloed.mm"
include "cc0.mm"
include "9nn.mm"
include "9p1e10.mm"
include "10re.mm"
include "10nn.mm"
include "dec10p.mm"
include "1nn.mm"
include "c2.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "nncni.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "1p1e2.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "3eqtri.mm"
include "2nn.mm"
include "wn.mm"
include "2cn.mm"
include "2p1e3.mm"
include "lenltd.mm"
include "pm2.21.mm"
include "syl6bi.mm"
include "com12.mm"
include "eleq1.mm"
include "ceven.mm"
include "c6.mm"
include "6p6e12.mm"
include "6even.mm"
include "epee.mm"
include "eqeltrri.mm"
include "evennodd.mm"
include "ax-mp.mm"
include "pm2.21i.mm"
include "syl6bir.mm"
include "jaoi.mm"
include "sylbid.mm"
include "11gbo.mm"
include "mpbii.mm"
include "2a1d.mm"
include "c5.mm"
include "5p5e10.mm"
include "5odd.mm"
include "opoeALTV.mm"
include "9gbo.mm"
include "8even.mm"
include "imp.mm"
include "3ad2ant3.mm"
include "syl5bi.mm"
include "3impia.mm"

theorem bgoldbtbndlem1
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. Odd /\ 7 < N /\ N e. ( 7 [,) ; 1 3 ) ) -> N e. GoldbachOdd )

  proof
    cN
    codd
    wcel
    #
    c7
    cN
    clt
    wbr
    #
    cN
    c7
    c1
    c3
    cdc
    #
    cico
    co
    wcel
    #
    cN
    cgbo
    wcel
    #
    @3
    cN
    cxr
    wcel
    #
    c7
    cN
    cle
    wbr
    #
    cN
    @2
    clt
    wbr
    #
    w3a
    #
    @0
    @1
    wa
    #
    @4
    c7
    cxr
    wcel
    @2
    cxr
    wcel
    @3
    @8
    wb
    c7
    7re
    rexri
    @2
    @2
    c1
    c3
    1nn0
    3nn
    decnncl
    nnrei
    #
    rexri
    c7
    @2
    cN
    elico1
    mp2an
    @8
    @9
    @4
    @7
    @5
    @9
    @4
    wi
    @6
    @9
    @7
    @4
    @0
    @1
    @7
    @4
    wi
    #
    @0
    @1
    c8
    cN
    clt
    wbr
    #
    c8
    cN
    wceq
    #
    wo
    #
    @11
    @0
    c7
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @1
    @14
    wb
    c7
    7nn
    nnzi
    cN
    oddz
    #
    @15
    @16
    wa
    #
    @1
    c7
    c1
    caddc
    co
    #
    cN
    cle
    wbr
    #
    c8
    cN
    cle
    wbr
    #
    @14
    c7
    cN
    zltp1le
    @20
    @21
    wb
    @18
    @19
    c8
    cN
    cle
    7p1e8
    breq1i
    a1i
    @15
    c8
    cr
    wcel
    #
    cN
    cr
    wcel
    @21
    @14
    wb
    @16
    @22
    @15
    8re
    a1i
    cN
    zre
    c8
    cN
    leloe
    syl2an
    3bitrd
    sylancr
    @14
    @0
    @11
    @12
    @0
    @11
    wi
    #
    @13
    @0
    @12
    @11
    @0
    @12
    c9
    cN
    clt
    wbr
    #
    c9
    cN
    wceq
    #
    wo
    #
    @11
    @0
    @12
    c8
    c1
    caddc
    co
    #
    cN
    cle
    wbr
    #
    c9
    cN
    cle
    wbr
    #
    @26
    @0
    c8
    cz
    wcel
    @16
    @12
    @28
    wb
    c8
    8nn
    nnzi
    @17
    c8
    cN
    zltp1le
    sylancr
    @28
    @29
    wb
    @0
    @27
    c9
    cN
    cle
    8p1e9
    breq1i
    a1i
    @0
    c9
    cN
    c9
    cr
    wcel
    @0
    9re
    a1i
    @0
    cN
    @17
    zred
    #
    leloed
    3bitrd
    @26
    @0
    @11
    @24
    @23
    @25
    @0
    @24
    @11
    @0
    @24
    c1
    cc0
    cdc
    #
    cN
    clt
    wbr
    #
    @31
    cN
    wceq
    #
    wo
    #
    @11
    @0
    @24
    c9
    c1
    caddc
    co
    #
    cN
    cle
    wbr
    #
    @31
    cN
    cle
    wbr
    #
    @34
    @0
    c9
    cz
    wcel
    @16
    @24
    @36
    wb
    c9
    9nn
    nnzi
    @17
    c9
    cN
    zltp1le
    sylancr
    @36
    @37
    wb
    @0
    @35
    @31
    cN
    cle
    9p1e10
    breq1i
    a1i
    @0
    @31
    cN
    @31
    cr
    wcel
    @0
    10re
    a1i
    @30
    leloed
    3bitrd
    @34
    @0
    @11
    @32
    @23
    @33
    @0
    @32
    @11
    @0
    @32
    c1
    c1
    cdc
    #
    cN
    clt
    wbr
    #
    @38
    cN
    wceq
    #
    wo
    #
    @11
    @0
    @32
    @31
    c1
    caddc
    co
    #
    cN
    cle
    wbr
    #
    @38
    cN
    cle
    wbr
    #
    @41
    @0
    @31
    cz
    wcel
    @16
    @32
    @43
    wb
    @31
    10nn
    nnzi
    @17
    @31
    cN
    zltp1le
    sylancr
    @43
    @44
    wb
    @0
    @42
    @38
    cN
    cle
    c1
    dec10p
    #
    breq1i
    a1i
    @0
    @38
    cN
    @38
    cr
    wcel
    @0
    @38
    c1
    c1
    1nn0
    1nn
    decnncl
    #
    nnrei
    a1i
    @30
    leloed
    3bitrd
    @41
    @0
    @11
    @39
    @23
    @40
    @0
    @39
    @11
    @0
    @39
    c1
    c2
    cdc
    #
    cN
    clt
    wbr
    #
    @47
    cN
    wceq
    #
    wo
    #
    @11
    @0
    @39
    @38
    c1
    caddc
    co
    #
    cN
    cle
    wbr
    #
    @47
    cN
    cle
    wbr
    #
    @50
    @0
    @38
    cz
    wcel
    @16
    @39
    @52
    wb
    @38
    @46
    nnzi
    @17
    @38
    cN
    zltp1le
    sylancr
    @52
    @53
    wb
    @0
    @51
    @47
    cN
    cle
    @51
    @42
    c1
    caddc
    co
    @31
    c1
    c1
    caddc
    co
    #
    caddc
    co
    #
    @47
    @38
    @42
    c1
    caddc
    @42
    @38
    @45
    eqcomi
    oveq1i
    @31
    c1
    c1
    @31
    10nn
    nncni
    #
    ax-1cn
    ax-1cn
    addassi
    @55
    @31
    c2
    caddc
    co
    #
    @47
    @54
    c2
    @31
    caddc
    1p1e2
    oveq2i
    c2
    dec10p
    #
    eqtri
    3eqtri
    breq1i
    a1i
    @0
    @47
    cN
    @47
    cr
    wcel
    @0
    @47
    c1
    c2
    1nn0
    2nn
    decnncl
    #
    nnrei
    a1i
    @30
    leloed
    3bitrd
    @50
    @0
    @11
    @48
    @23
    @49
    @0
    @48
    @11
    @0
    @48
    @7
    wn
    #
    @11
    @0
    @48
    @47
    c1
    caddc
    co
    #
    cN
    cle
    wbr
    #
    @2
    cN
    cle
    wbr
    #
    @60
    @0
    @47
    cz
    wcel
    @16
    @48
    @62
    wb
    @47
    @59
    nnzi
    @17
    @47
    cN
    zltp1le
    sylancr
    @62
    @63
    wb
    @0
    @61
    @2
    cN
    cle
    @61
    @57
    c1
    caddc
    co
    @31
    c2
    c1
    caddc
    co
    #
    caddc
    co
    #
    @2
    @47
    @57
    c1
    caddc
    @57
    @47
    @58
    eqcomi
    oveq1i
    @31
    c2
    c1
    @56
    2cn
    ax-1cn
    addassi
    @65
    @31
    c3
    caddc
    co
    @2
    @64
    c3
    @31
    caddc
    2p1e3
    oveq2i
    c3
    dec10p
    eqtri
    3eqtri
    breq1i
    a1i
    @0
    @2
    cN
    @2
    cr
    wcel
    @0
    @10
    a1i
    @30
    lenltd
    3bitrd
    @7
    @4
    pm2.21
    syl6bi
    com12
    @49
    @0
    @47
    codd
    wcel
    #
    @11
    @47
    cN
    codd
    eleq1
    @66
    @11
    @47
    ceven
    wcel
    @66
    wn
    c6
    c6
    caddc
    co
    #
    @47
    ceven
    6p6e12
    c6
    ceven
    wcel
    #
    @68
    @67
    ceven
    wcel
    6even
    6even
    c6
    c6
    epee
    mp2an
    eqeltrri
    @47
    evennodd
    ax-mp
    pm2.21i
    syl6bir
    jaoi
    com12
    sylbid
    com12
    @40
    @4
    @0
    @7
    @40
    @38
    cgbo
    wcel
    @4
    11gbo
    @38
    cN
    cgbo
    eleq1
    mpbii
    2a1d
    jaoi
    com12
    sylbid
    com12
    @33
    @0
    @31
    codd
    wcel
    #
    @11
    @31
    cN
    codd
    eleq1
    @69
    @11
    @31
    ceven
    wcel
    @69
    wn
    c5
    c5
    caddc
    co
    #
    @31
    ceven
    5p5e10
    c5
    codd
    wcel
    #
    @71
    @70
    ceven
    wcel
    5odd
    5odd
    c5
    c5
    opoeALTV
    mp2an
    eqeltrri
    @31
    evennodd
    ax-mp
    pm2.21i
    syl6bir
    jaoi
    com12
    sylbid
    com12
    @25
    @4
    @0
    @7
    @25
    c9
    cgbo
    wcel
    @4
    9gbo
    c9
    cN
    cgbo
    eleq1
    mpbii
    2a1d
    jaoi
    com12
    sylbid
    com12
    @13
    @0
    c8
    codd
    wcel
    #
    @11
    c8
    cN
    codd
    eleq1
    @72
    @11
    c8
    ceven
    wcel
    @72
    wn
    8even
    c8
    evennodd
    ax-mp
    pm2.21i
    syl6bir
    jaoi
    com12
    sylbid
    imp
    com12
    3ad2ant3
    com12
    syl5bi
    3impia
end
