include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cprime.mm"
include "wa.mm"
include "csgm.mm"
include "cmul.mm"
include "cn.mm"
include "wceq.mm"
include "mersenne.mm"
include "prmnn.mm"
include "syl.mm"
include "1sgm2ppw.mm"
include "caddc.mm"
include "1sgmprm.mm"
include "adantl.mm"
include "cc.mm"
include "cn0.mm"
include "2nn.mm"
include "nnnn0d.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "nncnd.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "cgcd.mm"
include "a1i.mm"
include "nnm1nn0.mm"
include "nnzd.mm"
include "prmz.mm"
include "gcdcom.mm"
include "syl2anc.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "iddvds.mm"
include "clt.mm"
include "wi.mm"
include "cuz.mm"
include "cfv.mm"
include "prmuz2.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "ndvdsp1.mm"
include "syl3anc.mm"
include "mpd.mm"
include "2z.mm"
include "dvdsmultr1.mm"
include "2cn.mm"
include "expm1t.mm"
include "eqtr2d.mm"
include "breq2d.mm"
include "sylibd.mm"
include "mtod.mm"
include "wb.mm"
include "simpr.mm"
include "coprm.mm"
include "mpbid.mm"
include "sgmmul.mm"
include "syl13anc.mm"
include "subcl.mm"
include "mulcomd.mm"
include "3eqtr4d.mm"

theorem perfect1
  let cP: class P
  let vk: setvar k
  let vn: setvar n


  assert |- ( ( P e. ZZ /\ ( ( 2 ^ P ) - 1 ) e. Prime ) -> ( 1 sigma ( ( 2 ^ ( P - 1 ) ) x. ( ( 2 ^ P ) - 1 ) ) ) = ( ( 2 ^ P ) x. ( ( 2 ^ P ) - 1 ) ) )

  proof
    cP
    cz
    wcel
    #
    c2
    cP
    cexp
    co
    #
    c1
    cmin
    co
    #
    cprime
    wcel
    #
    wa
    #
    c1
    c2
    cP
    c1
    cmin
    co
    #
    cexp
    co
    #
    csgm
    co
    #
    c1
    @2
    csgm
    co
    #
    cmul
    co
    #
    @2
    @1
    cmul
    co
    c1
    @6
    @2
    cmul
    co
    csgm
    co
    #
    @1
    @2
    cmul
    co
    @4
    @7
    @2
    @8
    @1
    cmul
    @4
    cP
    cn
    wcel
    #
    @7
    @2
    wceq
    @4
    cP
    cprime
    wcel
    @11
    cP
    mersenne
    cP
    prmnn
    syl
    #
    cP
    1sgm2ppw
    syl
    @4
    @8
    @2
    c1
    caddc
    co
    #
    @1
    @3
    @8
    @13
    wceq
    @0
    @2
    1sgmprm
    adantl
    @4
    @1
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @13
    @1
    wceq
    @4
    @1
    @4
    c2
    cn
    wcel
    #
    cP
    cn0
    wcel
    @1
    cn
    wcel
    2nn
    @4
    cP
    @12
    nnnn0d
    c2
    cP
    nnexpcl
    sylancr
    nncnd
    #
    ax-1cn
    @1
    c1
    npcan
    sylancl
    #
    eqtrd
    oveq12d
    @4
    @15
    @6
    cn
    wcel
    #
    @2
    cn
    wcel
    #
    @6
    @2
    cgcd
    co
    #
    c1
    wceq
    @10
    @9
    wceq
    @15
    @4
    ax-1cn
    a1i
    @4
    @16
    @5
    cn0
    wcel
    #
    @19
    2nn
    @4
    @11
    @22
    @12
    cP
    nnm1nn0
    syl
    c2
    @5
    nnexpcl
    sylancr
    #
    @3
    @20
    @0
    @2
    prmnn
    adantl
    #
    @4
    @21
    @2
    @6
    cgcd
    co
    #
    c1
    @4
    @6
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    @21
    @25
    wceq
    @4
    @6
    @23
    nnzd
    #
    @3
    @27
    @0
    @2
    prmz
    adantl
    #
    @6
    @2
    gcdcom
    syl2anc
    @4
    @2
    @6
    cdvds
    wbr
    #
    wn
    #
    @25
    c1
    wceq
    #
    @4
    @30
    @2
    @13
    cdvds
    wbr
    #
    @4
    @2
    @2
    cdvds
    wbr
    #
    @33
    wn
    #
    @4
    @27
    @34
    @29
    @2
    iddvds
    syl
    @4
    @27
    @20
    c1
    @2
    clt
    wbr
    #
    @34
    @35
    wi
    @29
    @24
    @4
    @2
    c2
    cuz
    cfv
    wcel
    #
    @36
    @3
    @37
    @0
    @2
    prmuz2
    adantl
    @37
    @20
    @36
    @2
    eluz2b2
    simprbi
    syl
    @2
    @2
    ndvdsp1
    syl3anc
    mpd
    @4
    @30
    @2
    @6
    c2
    cmul
    co
    #
    cdvds
    wbr
    #
    @33
    @4
    @27
    @26
    c2
    cz
    wcel
    #
    @30
    @39
    wi
    @29
    @28
    @40
    @4
    2z
    a1i
    @2
    @6
    c2
    dvdsmultr1
    syl3anc
    @4
    @38
    @13
    @2
    cdvds
    @4
    @13
    @1
    @38
    @18
    @4
    c2
    cc
    wcel
    @11
    @1
    @38
    wceq
    2cn
    @12
    c2
    cP
    expm1t
    sylancr
    eqtr2d
    breq2d
    sylibd
    mtod
    @4
    @3
    @26
    @31
    @32
    wb
    @0
    @3
    simpr
    @28
    @2
    @6
    coprm
    syl2anc
    mpbid
    eqtrd
    c1
    @6
    @2
    sgmmul
    syl13anc
    @4
    @1
    @2
    @17
    @4
    @14
    @15
    @2
    cc
    wcel
    @17
    ax-1cn
    @1
    c1
    subcl
    sylancl
    mulcomd
    3eqtr4d
end
