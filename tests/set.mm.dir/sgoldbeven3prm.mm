include "c4.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cgbe.mm"
include "wcel.mm"
include "wi.mm"
include "ceven.mm"
include "wral.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cprime.mm"
include "wrex.mm"
include "c6.mm"
include "cle.mm"
include "wa.mm"
include "sbgoldbb.mm"
include "cmin.mm"
include "2p2e4.mm"
include "cr.mm"
include "evenz.mm"
include "zred.mm"
include "4lt6.mm"
include "4re.mm"
include "6re.mm"
include "ltletr.mm"
include "mp3an12.mm"
include "mpani.mm"
include "syl.mm"
include "imp.mm"
include "syl5eqbr.mm"
include "2re.mm"
include "a1i.mm"
include "adantr.mm"
include "ltaddsub2d.mm"
include "mpbid.mm"
include "2evenALTV.mm"
include "emee.mm"
include "mpan2.mm"
include "breq2.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "2prm.mm"
include "wb.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "cc.mm"
include "zcnd.mm"
include "2cnd.mm"
include "npcan.mm"
include "eqcomd.mm"
include "syl2anc.mm"
include "simpr.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "rspcedvd.mm"
include "ex.mm"
include "reximdv.mm"
include "imim2d.mm"
include "syl9r.mm"
include "mpd.mm"
include "mpid.mm"
include "syl5com.mm"

theorem sgoldbeven3prm
  let vn: setvar n
  let cN: class N
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x

  disjoint N n
  disjoint N p
  disjoint N q
  disjoint N r
  disjoint n p
  disjoint n q
  disjoint n r
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint k x
  assert |- ( A. n e. Even ( 4 < n -> n e. GoldbachEven ) -> ( ( N e. Even /\ 6 <_ N ) -> E. p e. Prime E. q e. Prime E. r e. Prime N = ( ( p + q ) + r ) ) )

  proof
    c4
    vn
    cv
    #
    clt
    wbr
    @0
    cgbe
    wcel
    wi
    vn
    ceven
    wral
    c2
    @0
    clt
    wbr
    #
    @0
    vp
    cv
    vq
    cv
    caddc
    co
    #
    wceq
    #
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    #
    wi
    #
    vn
    ceven
    wral
    #
    cN
    ceven
    wcel
    #
    c6
    cN
    cle
    wbr
    #
    wa
    #
    cN
    @2
    vr
    cv
    #
    caddc
    co
    #
    wceq
    #
    vr
    cprime
    wrex
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    #
    vn
    vq
    vp
    sbgoldbb
    @9
    @6
    c2
    cN
    c2
    cmin
    co
    #
    clt
    wbr
    #
    @15
    @9
    c2
    c2
    caddc
    co
    #
    cN
    clt
    wbr
    @17
    @9
    @18
    c4
    cN
    clt
    2p2e4
    @7
    @8
    c4
    cN
    clt
    wbr
    #
    @7
    cN
    cr
    wcel
    #
    @8
    @19
    wi
    @7
    cN
    cN
    evenz
    #
    zred
    #
    @20
    c4
    c6
    clt
    wbr
    #
    @8
    @19
    4lt6
    c4
    cr
    wcel
    c6
    cr
    wcel
    @20
    @23
    @8
    wa
    @19
    wi
    4re
    6re
    c4
    c6
    cN
    ltletr
    mp3an12
    mpani
    syl
    imp
    syl5eqbr
    @9
    c2
    c2
    cN
    c2
    cr
    wcel
    @9
    2re
    a1i
    #
    @24
    @7
    @20
    @8
    @22
    adantr
    ltaddsub2d
    mpbid
    @7
    @6
    @17
    @15
    wi
    #
    wi
    #
    @8
    @7
    @16
    ceven
    wcel
    #
    @26
    @7
    c2
    ceven
    wcel
    @27
    2evenALTV
    cN
    c2
    emee
    mpan2
    @27
    @6
    @17
    @16
    @2
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
    @7
    @25
    @5
    @31
    vn
    @16
    ceven
    @0
    @16
    wceq
    #
    @1
    @17
    @4
    @30
    @0
    @16
    c2
    clt
    breq2
    @32
    @3
    @28
    vp
    vq
    cprime
    cprime
    @0
    @16
    @2
    eqeq1
    2rexbidv
    imbi12d
    rspcv
    @7
    @30
    @15
    @17
    @7
    @29
    @14
    vp
    cprime
    @7
    @28
    @13
    vq
    cprime
    @7
    @28
    @13
    @7
    @28
    wa
    #
    @12
    cN
    @2
    c2
    caddc
    co
    #
    wceq
    #
    vr
    c2
    cprime
    c2
    cprime
    wcel
    @33
    2prm
    a1i
    @10
    c2
    wceq
    #
    @12
    @35
    wb
    @33
    @36
    @11
    @34
    cN
    @10
    c2
    @2
    caddc
    oveq2
    eqeq2d
    adantl
    @33
    cN
    @16
    c2
    caddc
    co
    #
    @34
    @7
    cN
    @37
    wceq
    #
    @28
    @7
    cN
    cc
    wcel
    #
    c2
    cc
    wcel
    #
    @38
    @7
    cN
    @21
    zcnd
    @7
    2cnd
    @39
    @40
    wa
    @37
    cN
    cN
    c2
    npcan
    eqcomd
    syl2anc
    adantr
    @33
    @16
    @2
    c2
    caddc
    @7
    @28
    simpr
    oveq1d
    eqtrd
    rspcedvd
    ex
    reximdv
    reximdv
    imim2d
    syl9r
    mpd
    adantr
    mpid
    syl5com
end
