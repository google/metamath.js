include "wwe.mm"
include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "copab.mm"
include "cxp.mm"
include "cin.mm"
include "cc0.mm"
include "cfsupp.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "coi.mm"
include "chash.mm"
include "com.mm"
include "cres.mm"
include "eqid.mm"
include "breq1.mm"
include "cbvrabv.mm"
include "cuz.mm"
include "nn0uz.mm"
include "ltweuz.mm"
include "weeq2.mm"
include "mpbiri.mm"
include "mp1i.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "0nn0.mm"
include "ne0i.mm"
include "0z.mm"
include "hashgval2.mm"
include "om2uzoi.mm"
include "oieq2.mm"
include "ax-mp.mm"
include "eqtr4i.mm"
include "peano1.mm"
include "fvres.mm"
include "hash0.mm"
include "eqtr2i.mm"
include "wemapwe.mm"
include "wb.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "csupp.mm"
include "wfun.mm"
include "cvv.mm"
include "elmapfun.mm"
include "adantl.mm"
include "simpr.mm"
include "c0ex.mm"
include "a1i.mm"
include "funisfsupp.mm"
include "syl3anc.mm"
include "wf.mm"
include "elmapi.mm"
include "frnnn0supp.mm"
include "eleq1d.mm"
include "syl2an.mm"
include "bitr2d.mm"
include "rabbidva.mm"
include "syl5eq.mm"
include "syl.mm"
include "mpbird.mm"
include "weinxp.mm"
include "sylib.mm"
include "cpr.mm"
include "wss.mm"
include "ltbval.mm"
include "df-xp.mm"
include "vex.mm"
include "prss.mm"
include "opabbii.mm"
include "ineq1i.mm"
include "inopab.mm"
include "incom.mm"
include "3eqtr3i.mm"
include "syl6eq.mm"
include "weeq1.mm"

theorem ltbwe
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cT: class T
  let vh: setvar h
  let cI: class I
  let cV: class V
  let cW: class W
  let vi: setvar i
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  assume ltbval.c: |- C = ( T <bag I )
  assume ltbval.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume ltbval.i: |- ( ph -> I e. V )
  assume ltbval.t: |- ( ph -> T e. W )
  assume ltbwe.w: |- ( ph -> T We I )

  disjoint I h
  disjoint h ph
  disjoint i r
  disjoint i x
  disjoint i y
  disjoint D i
  disjoint r x
  disjoint r y
  disjoint D r
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint h i
  disjoint h r
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint i w
  disjoint i z
  disjoint I i
  disjoint r w
  disjoint r z
  disjoint I r
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint I w
  disjoint x z
  disjoint I x
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint ph x
  disjoint ph y
  disjoint T i
  disjoint T r
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ph -> C We D )

  proof
    wph
    cD
    cC
    wwe
    #
    cD
    vz
    cv
    #
    vx
    cv
    #
    cfv
    @1
    vy
    cv
    #
    cfv
    clt
    wbr
    @1
    vw
    cv
    #
    cT
    wbr
    @4
    @2
    cfv
    @4
    @3
    cfv
    wceq
    wi
    vw
    cI
    wral
    wa
    vz
    cI
    wrex
    #
    vx
    vy
    copab
    #
    cD
    cD
    cxp
    #
    cin
    #
    wwe
    #
    wph
    cD
    @6
    wwe
    #
    @9
    wph
    @10
    vh
    cv
    #
    cc0
    cfsupp
    wbr
    #
    vh
    cn0
    cI
    cmap
    co
    #
    crab
    #
    @6
    wwe
    #
    wph
    vx
    vy
    vz
    vw
    cI
    cn0
    cT
    clt
    @6
    @14
    cI
    cT
    coi
    #
    chash
    com
    cres
    #
    cc0
    @6
    eqid
    @12
    @2
    cc0
    cfsupp
    wbr
    vh
    vx
    @13
    @11
    @2
    cc0
    cfsupp
    breq1
    cbvrabv
    ltbwe.w
    cn0
    cc0
    cuz
    cfv
    #
    wceq
    #
    cn0
    clt
    wwe
    #
    wph
    nn0uz
    @19
    @20
    @18
    clt
    wwe
    cc0
    ltweuz
    cn0
    @18
    clt
    weeq2
    mpbiri
    mp1i
    cc0
    cn0
    wcel
    cn0
    c0
    wne
    wph
    0nn0
    cn0
    cc0
    ne0i
    mp1i
    @16
    eqid
    @17
    @18
    clt
    coi
    #
    cn0
    clt
    coi
    #
    vx
    cc0
    @17
    0z
    vx
    hashgval2
    om2uzoi
    @19
    @22
    @21
    wceq
    nn0uz
    cn0
    @18
    clt
    oieq2
    ax-mp
    eqtr4i
    c0
    @17
    cfv
    #
    c0
    chash
    cfv
    #
    cc0
    c0
    com
    wcel
    @23
    @24
    wceq
    peano1
    c0
    com
    chash
    fvres
    ax-mp
    hash0
    eqtr2i
    wemapwe
    wph
    cD
    @14
    wceq
    @10
    @15
    wb
    wph
    cD
    @11
    ccnv
    cn
    cima
    #
    cfn
    wcel
    #
    vh
    @13
    crab
    @14
    ltbval.d
    wph
    @26
    @12
    vh
    @13
    wph
    @11
    @13
    wcel
    #
    wa
    #
    @12
    @11
    cc0
    csupp
    co
    #
    cfn
    wcel
    #
    @26
    @28
    @11
    wfun
    #
    @27
    cc0
    cvv
    wcel
    #
    @12
    @30
    wb
    @27
    @31
    wph
    @11
    cn0
    cI
    elmapfun
    adantl
    wph
    @27
    simpr
    @32
    @28
    c0ex
    a1i
    @11
    @13
    cvv
    cc0
    funisfsupp
    syl3anc
    wph
    cI
    cV
    wcel
    #
    cI
    cn0
    @11
    wf
    #
    @30
    @26
    wb
    @27
    ltbval.i
    @11
    cn0
    cI
    elmapi
    @33
    @34
    wa
    @29
    @25
    cfn
    @11
    cI
    cV
    frnnn0supp
    eleq1d
    syl2an
    bitr2d
    rabbidva
    syl5eq
    cD
    @14
    @6
    weeq2
    syl
    mpbird
    cD
    @6
    weinxp
    sylib
    wph
    cC
    @8
    wceq
    @0
    @9
    wb
    wph
    cC
    @2
    @3
    cpr
    cD
    wss
    #
    @5
    wa
    vx
    vy
    copab
    #
    @8
    wph
    vx
    vy
    vz
    vw
    cC
    cD
    cT
    vh
    cI
    cV
    cW
    ltbval.c
    ltbval.d
    ltbval.i
    ltbval.t
    ltbval
    @35
    vx
    vy
    copab
    #
    @6
    cin
    @7
    @6
    cin
    @36
    @8
    @37
    @7
    @6
    @7
    @2
    cD
    wcel
    @3
    cD
    wcel
    wa
    #
    vx
    vy
    copab
    @37
    vx
    vy
    cD
    cD
    df-xp
    @38
    @35
    vx
    vy
    @2
    @3
    cD
    vx
    vex
    vy
    vex
    prss
    opabbii
    eqtr2i
    ineq1i
    @35
    @5
    vx
    vy
    inopab
    @7
    @6
    incom
    3eqtr3i
    syl6eq
    cD
    cC
    @8
    weeq1
    syl
    mpbird
end
