include "cfv.mm"
include "cabs.mm"
include "c1.mm"
include "cr.mm"
include "ffvelrnd.mm"
include "recnd.mm"
include "abscld.mm"
include "1red.mm"
include "clt.mm"
include "wbr.mm"
include "simpr.mm"
include "wa.mm"
include "wf.mm"
include "adantr.mm"
include "wcel.mm"
include "cima.mm"
include "csup.mm"
include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "cmul.mm"
include "cc.mm"
include "ax-resscn.mm"
include "ccom.mm"
include "imaco.mm"
include "eqcomi.mm"
include "crn.mm"
include "wss.mm"
include "imassrn.mm"
include "a1i.mm"
include "absf.mm"
include "fssresd.mm"
include "fco2d.mm"
include "frn.mm"
include "syl.mm"
include "sstrd.mm"
include "syl5eqss.mm"
include "c0.mm"
include "wne.mm"
include "cc0.mm"
include "0re.mm"
include "ne0ii.mm"
include "wnefimgd.mm"
include "necomd.mm"
include "wceq.mm"
include "neeqtrrd.mm"
include "cv.mm"
include "wral.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "extoimad.mm"
include "rspcedvd.mm"
include "suprcld.mm"
include "sseldi.mm"
include "mulcomd.mm"
include "0lt1.mm"
include "lttrd.mm"
include "gt0ne0d.mm"
include "redivcld.mm"
include "caddc.mm"
include "cmin.mm"
include "c2.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "wi.mm"
include "ralcom2.mm"
include "imp.mm"
include "mpdan.mm"
include "rspcdvinvd.mm"
include "r19.21bi.mm"
include "adantlr.mm"
include "ad2antrr.mm"
include "imo72b2lem0.mm"
include "cxr.mm"
include "0xr.mm"
include "1re.mm"
include "rexri.mm"
include "rexrd.mm"
include "simplr.mm"
include "xrlttrd.mm"
include "ffvelrnda.mm"
include "lemuldiv3d.mm"
include "ralrimiva.mm"
include "imo72b2lem2.mm"
include "lemuldiv4d.mm"
include "eqbrtrrd.mm"
include "wrex.mm"
include "imo72b2lem1.mm"
include "sseldd.mm"
include "dividd.mm"
include "eqcomd.mm"
include "breqtrrd.mm"
include "lensymd.mm"
include "pm2.65da.mm"
include "nltled.mm"

theorem imo72b2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let cF: class F
  let cG: class G
  let vc: setvar c
  let vt: setvar t
  assume imo72b2.1: |- ( ph -> F : RR --> RR )
  assume imo72b2.2: |- ( ph -> G : RR --> RR )
  assume imo72b2.4: |- ( ph -> B e. RR )
  assume imo72b2.5: |- ( ph -> A. u e. RR A. v e. RR ( ( F ` ( u + v ) ) + ( F ` ( u - v ) ) ) = ( 2 x. ( ( F ` u ) x. ( G ` v ) ) ) )
  assume imo72b2.6: |- ( ph -> A. y e. RR ( abs ` ( F ` y ) ) <_ 1 )
  assume imo72b2.7: |- ( ph -> E. x e. RR ( F ` x ) =/= 0 )

  disjoint B u
  disjoint B v
  disjoint u v
  disjoint B x
  disjoint B y
  disjoint F u
  disjoint F v
  disjoint F x
  disjoint F y
  disjoint G u
  disjoint G v
  disjoint G x
  disjoint G y
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint u y
  disjoint B c
  disjoint B t
  disjoint c t
  disjoint t y
  disjoint F c
  disjoint F t
  disjoint G c
  disjoint G t
  disjoint c ph
  disjoint ph t
  assert |- ( ph -> ( abs ` ( G ` B ) ) <_ 1 )

  proof
    wph
    cB
    cG
    cfv
    #
    cabs
    cfv
    #
    c1
    wph
    @0
    wph
    @0
    wph
    cr
    cr
    cB
    cG
    imo72b2.2
    imo72b2.4
    ffvelrnd
    recnd
    abscld
    wph
    1red
    #
    wph
    c1
    @1
    clt
    wbr
    #
    @3
    wph
    @3
    simpr
    #
    wph
    @3
    wa
    #
    @1
    c1
    @5
    @0
    @5
    @0
    @5
    cr
    cr
    cB
    cG
    wph
    cr
    cr
    cG
    wf
    #
    @3
    imo72b2.2
    adantr
    #
    wph
    cB
    cr
    wcel
    #
    @3
    imo72b2.4
    adantr
    #
    ffvelrnd
    recnd
    abscld
    #
    wph
    c1
    cr
    wcel
    @3
    @2
    adantr
    #
    @5
    @1
    cabs
    cF
    cr
    cima
    cima
    #
    cr
    clt
    csup
    #
    @13
    cdiv
    co
    #
    c1
    cle
    @5
    @13
    @1
    @13
    @5
    @13
    @1
    cmul
    co
    @1
    @13
    cmul
    co
    @13
    cle
    @5
    @13
    @1
    @5
    cr
    cc
    @13
    ax-resscn
    @5
    vc
    vt
    @12
    @5
    @12
    cabs
    cF
    ccom
    #
    cr
    cima
    #
    cr
    @16
    @12
    cabs
    cF
    cr
    imaco
    eqcomi
    #
    @5
    @16
    @15
    crn
    #
    cr
    @16
    @18
    wss
    @5
    @15
    cr
    imassrn
    a1i
    @5
    cr
    cr
    @15
    wf
    @18
    cr
    wss
    @5
    cr
    cr
    cr
    cabs
    cF
    wph
    cr
    cr
    cF
    wf
    #
    @3
    imo72b2.1
    adantr
    #
    @5
    cc
    cr
    cr
    cabs
    cc
    cr
    cabs
    wf
    @5
    absf
    a1i
    cr
    cc
    wss
    @5
    ax-resscn
    a1i
    #
    fssresd
    fco2d
    #
    cr
    cr
    @15
    frn
    syl
    sstrd
    syl5eqss
    @5
    c0
    @12
    @5
    c0
    @16
    @12
    @5
    @16
    c0
    @5
    cr
    cr
    @15
    cr
    c0
    wne
    @5
    cc0
    cr
    0re
    ne0ii
    a1i
    @22
    wnefimgd
    necomd
    @12
    @16
    wceq
    @5
    @17
    a1i
    neeqtrrd
    necomd
    @5
    vt
    cv
    #
    vc
    cv
    #
    cle
    wbr
    #
    vt
    @12
    wral
    @23
    c1
    cle
    wbr
    #
    vt
    @12
    wral
    #
    vc
    c1
    cr
    @11
    @5
    @24
    c1
    wceq
    #
    wa
    #
    @25
    @26
    vt
    @12
    @29
    @24
    c1
    @23
    cle
    @5
    @28
    simpr
    breq2d
    ralbidv
    wph
    @27
    @3
    wph
    vt
    vy
    c1
    cF
    imo72b2.1
    imo72b2.6
    extoimad
    adantr
    rspcedvd
    suprcld
    #
    sseldi
    @5
    cr
    cc
    @1
    ax-resscn
    @10
    sseldi
    mulcomd
    @5
    @1
    @13
    @13
    @5
    vu
    @13
    @1
    cdiv
    co
    #
    cF
    @20
    @5
    @13
    @1
    @30
    @10
    @5
    @1
    @5
    cc0
    c1
    @1
    cc0
    cr
    wcel
    @5
    0re
    a1i
    @11
    @10
    cc0
    c1
    clt
    wbr
    #
    @5
    0lt1
    a1i
    @4
    lttrd
    #
    gt0ne0d
    redivcld
    @5
    vu
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    @31
    cle
    wbr
    vu
    cr
    @5
    @34
    cr
    wcel
    #
    wa
    #
    @1
    @36
    @13
    @38
    vy
    @34
    cB
    cF
    cG
    @5
    @19
    @37
    @20
    adantr
    @5
    @6
    @37
    @7
    adantr
    @5
    @37
    simpr
    @5
    @8
    @37
    @9
    adantr
    wph
    @37
    @34
    cB
    caddc
    co
    #
    cF
    cfv
    #
    @34
    cB
    cmin
    co
    #
    cF
    cfv
    #
    caddc
    co
    #
    c2
    @35
    @0
    cmul
    co
    #
    cmul
    co
    #
    wceq
    #
    @3
    wph
    @46
    vu
    cr
    wph
    @34
    vv
    cv
    #
    caddc
    co
    #
    cF
    cfv
    #
    @34
    @47
    cmin
    co
    #
    cF
    cfv
    #
    caddc
    co
    #
    c2
    @35
    @47
    cG
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    wceq
    #
    vu
    cr
    wral
    #
    @46
    vu
    cr
    wral
    vv
    cB
    cr
    wph
    @47
    cB
    wceq
    #
    wa
    #
    @56
    @46
    vu
    cr
    @59
    @52
    @43
    @55
    @45
    @59
    @49
    @40
    @51
    @42
    caddc
    @59
    @48
    @39
    cF
    @59
    @47
    cB
    @34
    caddc
    wph
    @58
    simpr
    #
    oveq2d
    fveq2d
    @59
    @50
    @41
    cF
    @59
    @47
    cB
    @34
    cmin
    @60
    oveq2d
    fveq2d
    oveq12d
    @59
    @54
    @44
    c2
    cmul
    @59
    @53
    @0
    @35
    cmul
    @59
    @47
    cB
    cG
    @60
    fveq2d
    oveq2d
    oveq2d
    eqeq12d
    ralbidv
    imo72b2.4
    wph
    @56
    vv
    cr
    wral
    vu
    cr
    wral
    #
    @57
    vv
    cr
    wral
    #
    imo72b2.5
    wph
    @61
    @62
    @61
    @62
    wi
    wph
    @56
    vu
    vv
    cr
    ralcom2
    a1i
    imp
    mpdan
    rspcdvinvd
    r19.21bi
    adantlr
    wph
    vy
    cv
    cF
    cfv
    cabs
    cfv
    c1
    cle
    wbr
    vy
    cr
    wral
    #
    @3
    @37
    imo72b2.6
    ad2antrr
    imo72b2lem0
    @38
    cc0
    c1
    @1
    cc0
    cxr
    wcel
    @38
    0xr
    a1i
    c1
    cxr
    wcel
    @38
    c1
    1re
    rexri
    a1i
    @38
    @1
    @5
    @1
    cr
    wcel
    @37
    @10
    adantr
    #
    rexrd
    @32
    @38
    0lt1
    a1i
    wph
    @3
    @37
    simplr
    xrlttrd
    @64
    @38
    @35
    @38
    @35
    @5
    cr
    cr
    @34
    cF
    @20
    ffvelrnda
    recnd
    abscld
    @5
    @13
    cr
    wcel
    @37
    @30
    adantr
    lemuldiv3d
    ralrimiva
    imo72b2lem2
    @33
    @10
    @30
    @30
    lemuldiv4d
    eqbrtrrd
    @5
    vx
    vy
    cF
    @20
    wph
    vx
    cv
    cF
    cfv
    cc0
    wne
    vx
    cr
    wrex
    @3
    imo72b2.7
    adantr
    wph
    @63
    @3
    imo72b2.6
    adantr
    imo72b2lem1
    #
    @30
    @10
    @30
    lemuldiv3d
    @5
    @14
    c1
    @5
    @13
    @5
    cr
    cc
    @13
    @21
    @30
    sseldd
    @5
    @13
    @65
    gt0ne0d
    dividd
    eqcomd
    breqtrrd
    lensymd
    pm2.65da
    nltled
end
