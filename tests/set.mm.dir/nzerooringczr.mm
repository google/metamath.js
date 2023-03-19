include "czeroo.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "ax-1.mm"
include "wn.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "neq0.mm"
include "wa.mm"
include "cbs.mm"
include "cinito.mm"
include "ctermo.mm"
include "ccat.mm"
include "ringccat.mm"
include "syl.mm"
include "iszeroi.mm"
include "sylan.mm"
include "zrtermoringc.mm"
include "zring.mm"
include "irinitoringc.mm"
include "ccic.mm"
include "wbr.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "initoeu1w.mm"
include "termoeu1w.mm"
include "w3a.mm"
include "cictr.mm"
include "syl3an1.mm"
include "ciso.mm"
include "co.mm"
include "eqid.mm"
include "crg.mm"
include "cin.mm"
include "cnzr.mm"
include "eldifad.mm"
include "elind.mm"
include "ringcbas.mm"
include "eleqtrrd.mm"
include "zringring.mm"
include "a1i.mm"
include "cic.mm"
include "wne.mm"
include "n0.mm"
include "chom.mm"
include "wss.mm"
include "isohom.mm"
include "ssn0.mm"
include "crh.mm"
include "ringchom.mm"
include "neeq1d.mm"
include "cdif.mm"
include "zringnzr.mm"
include "nrhmzr.mm"
include "sylancl.mm"
include "eqneqall.mm"
include "sylbid.mm"
include "syl5com.mm"
include "expcom.mm"
include "com13.mm"
include "mpd.mm"
include "syl5bir.mm"
include "3ad2ant1.mm"
include "3exp.mm"
include "a1dd.mm"
include "exp31.mm"
include "com34.mm"
include "com25.mm"
include "ex.mm"
include "expimpd.mm"
include "com23.mm"
include "impd.mm"
include "com24.mm"
include "adantr.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "pm2.61i.mm"

theorem nzerooringczr
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cV: class V
  let cZ: class Z
  let vf: setvar f
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x
  assume nzerooringczr.u: |- ( ph -> U e. V )
  assume nzerooringczr.c: |- C = ( RingCat ` U )
  assume nzerooringczr.z: |- ( ph -> Z e. ( Ring \ NzRing ) )
  assume nzerooringczr.e: |- ( ph -> Z e. U )
  assume nzerooringczr.i: |- ( ph -> ZZring e. U )


  assert |- ( ph -> ( ZeroO ` C ) = (/) )

  proof
    cC
    czeroo
    cfv
    #
    c0
    wceq
    #
    wph
    @1
    wi
    #
    @1
    wph
    ax-1
    @1
    wn
    vh
    cv
    #
    @0
    wcel
    #
    vh
    wex
    @2
    vh
    @0
    neq0
    @4
    @2
    vh
    wph
    @4
    @1
    wph
    @4
    wa
    @3
    cC
    cbs
    cfv
    #
    wcel
    #
    @3
    cC
    cinito
    cfv
    #
    wcel
    #
    @3
    cC
    ctermo
    cfv
    #
    wcel
    #
    wa
    #
    wa
    #
    @1
    wph
    cC
    ccat
    wcel
    #
    @4
    @12
    wph
    cU
    cV
    wcel
    @13
    nzerooringczr.u
    cC
    cU
    cV
    nzerooringczr.c
    ringccat
    syl
    #
    cC
    @3
    iszeroi
    sylan
    wph
    @12
    @1
    wi
    #
    @4
    wph
    cZ
    @9
    wcel
    #
    @15
    wph
    cC
    cU
    cV
    cZ
    nzerooringczr.u
    nzerooringczr.c
    nzerooringczr.z
    nzerooringczr.e
    zrtermoringc
    wph
    zring
    @7
    wcel
    #
    @16
    @15
    wi
    wph
    cC
    cU
    cV
    nzerooringczr.u
    nzerooringczr.i
    nzerooringczr.c
    irinitoringc
    wph
    @12
    @16
    @17
    @1
    wph
    @6
    @11
    @16
    @17
    @1
    wi
    wi
    #
    wph
    @11
    @6
    @18
    wph
    @8
    @10
    @6
    @18
    wi
    wph
    @8
    wa
    #
    @17
    @6
    @16
    @10
    @1
    @19
    @17
    @6
    @16
    @10
    @1
    wi
    wi
    wi
    #
    @19
    @17
    wa
    #
    @3
    zring
    cC
    ccic
    cfv
    #
    wbr
    #
    @20
    @21
    @3
    zring
    cC
    wph
    @13
    @8
    @17
    @14
    ad2antrr
    wph
    @8
    @17
    simplr
    @19
    @17
    simpr
    initoeu1w
    wph
    @23
    @20
    wi
    @8
    @17
    wph
    @10
    @6
    @16
    @23
    @1
    wph
    @10
    @16
    @6
    @23
    @1
    wi
    #
    wph
    @10
    @16
    @6
    @24
    wi
    #
    wph
    @10
    wa
    #
    @16
    wa
    #
    cZ
    @3
    @22
    wbr
    #
    @25
    @27
    cZ
    @3
    cC
    wph
    @13
    @10
    @16
    @14
    ad2antrr
    @26
    @16
    simpr
    wph
    @10
    @16
    simplr
    termoeu1w
    wph
    @28
    @25
    wi
    @10
    @16
    wph
    @28
    @24
    @6
    wph
    @28
    @23
    @1
    wph
    @28
    @23
    w3a
    cZ
    zring
    @22
    wbr
    #
    @1
    wph
    @13
    @28
    @23
    @29
    @14
    cC
    cZ
    @3
    zring
    cictr
    syl3an1
    wph
    @28
    @29
    @1
    wi
    @23
    wph
    @29
    vf
    cv
    cZ
    zring
    cC
    ciso
    cfv
    #
    co
    #
    wcel
    vf
    wex
    #
    @1
    wph
    @5
    cC
    vf
    @30
    cZ
    zring
    @30
    eqid
    #
    @5
    eqid
    #
    @14
    wph
    cZ
    cU
    crg
    cin
    #
    @5
    wph
    cU
    crg
    cZ
    nzerooringczr.e
    wph
    cZ
    crg
    cnzr
    nzerooringczr.z
    eldifad
    elind
    wph
    @5
    cC
    cU
    cV
    nzerooringczr.c
    @34
    nzerooringczr.u
    ringcbas
    #
    eleqtrrd
    #
    wph
    zring
    @35
    @5
    wph
    cU
    crg
    zring
    nzerooringczr.i
    zring
    crg
    wcel
    wph
    zringring
    a1i
    elind
    @36
    eleqtrrd
    #
    cic
    @32
    @31
    c0
    wne
    #
    wph
    @1
    vf
    @31
    n0
    wph
    @31
    cZ
    zring
    cC
    chom
    cfv
    #
    co
    #
    wss
    #
    @39
    @1
    wi
    wph
    @5
    cC
    @40
    @30
    cZ
    zring
    @34
    @40
    eqid
    #
    @33
    @14
    @37
    @38
    isohom
    @39
    @42
    wph
    @1
    @42
    @39
    @2
    @42
    @39
    wa
    @41
    c0
    wne
    #
    wph
    @1
    @31
    @41
    ssn0
    wph
    @44
    cZ
    zring
    crh
    co
    #
    c0
    wne
    #
    @1
    wph
    @41
    @45
    c0
    wph
    @5
    cC
    cU
    @40
    cV
    cZ
    zring
    nzerooringczr.c
    @34
    nzerooringczr.u
    @43
    @37
    @38
    ringchom
    neeq1d
    wph
    @45
    c0
    wceq
    #
    @46
    @1
    wi
    wph
    cZ
    crg
    cnzr
    cdif
    wcel
    zring
    cnzr
    wcel
    @47
    nzerooringczr.z
    zringnzr
    zring
    cZ
    nrhmzr
    sylancl
    @1
    @45
    c0
    eqneqall
    syl
    sylbid
    syl5com
    expcom
    com13
    mpd
    syl5bir
    sylbid
    3ad2ant1
    mpd
    3exp
    a1dd
    ad2antrr
    mpd
    exp31
    com34
    com25
    ad2antrr
    mpd
    ex
    com25
    expimpd
    com23
    impd
    com24
    mpd
    mpd
    adantr
    mpd
    expcom
    exlimiv
    sylbi
    pm2.61i
end
