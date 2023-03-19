include "cxr.mm"
include "wss.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wrex.mm"
include "cr.mm"
include "wral.mm"
include "clt.mm"
include "csup.mm"
include "cpnf.mm"
include "wceq.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "wcel.mm"
include "ssel.mm"
include "pnfnlt.mm"
include "syl6.mm"
include "ralrimiv.mm"
include "adantr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "peano2re.mm"
include "breq1.mm"
include "rexbidv.mm"
include "rspcva.mm"
include "adantrr.mm"
include "ancoms.mm"
include "sylan2.mm"
include "ssel2.mm"
include "ltp1.mm"
include "ancli.mm"
include "rexr.mm"
include "xrltletr.mm"
include "syl3an2.mm"
include "syl3an1.mm"
include "3expa.mm"
include "sylan.mm"
include "mpand.mm"
include "an32s.mm"
include "reximdva.mm"
include "adantll.mm"
include "mpd.mm"
include "exp31.mm"
include "a1dd.mm"
include "com4r.mm"
include "com13.mm"
include "imp.mm"
include "jca.mm"
include "pnfxr.mm"
include "supxr.mm"
include "mpanl2.mm"
include "syldan.mm"
include "ex.mm"
include "ad2antlr.mm"
include "ltpnf.mm"
include "breq2.mm"
include "syl5ibr.mm"
include "impcom.mm"
include "wor.mm"
include "xrltso.mm"
include "a1i.mm"
include "xrsupss.mm"
include "ad2antrr.mm"
include "suplub.mm"
include "mp2and.mm"
include "adantlr.mm"
include "xrltle.mm"
include "syl2anc.mm"
include "syld.mm"
include "ralrimdva.mm"
include "impbid.mm"

theorem supxrunb1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let vw: setvar w
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B w
  assert |- ( A C_ RR* -> ( A. x e. RR E. y e. A x <_ y <-> sup ( A , RR* , < ) = +oo ) )

  proof
    cA
    cxr
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vy
    cA
    wrex
    #
    vx
    cr
    wral
    #
    cA
    cxr
    clt
    csup
    #
    cpnf
    wceq
    #
    @0
    @5
    @7
    @0
    @5
    cpnf
    vz
    cv
    #
    clt
    wbr
    wn
    #
    vz
    cA
    wral
    #
    @8
    cpnf
    clt
    wbr
    #
    @8
    @2
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    wi
    #
    vz
    cr
    wral
    #
    wa
    #
    @7
    @0
    @5
    wa
    #
    @10
    @15
    @0
    @10
    @5
    @0
    @9
    vz
    cA
    @0
    @8
    cA
    wcel
    @8
    cxr
    wcel
    #
    @9
    cA
    cxr
    @8
    ssel
    @8
    pnfnlt
    syl6
    ralrimiv
    adantr
    @17
    @14
    vz
    cr
    @0
    @5
    @8
    cr
    wcel
    #
    @14
    wi
    @19
    @5
    @0
    @14
    @5
    @0
    @11
    @19
    @13
    @5
    @0
    @19
    @13
    wi
    @11
    @5
    @0
    @19
    @13
    @5
    @0
    wa
    #
    @19
    wa
    @8
    c1
    caddc
    co
    #
    @2
    cle
    wbr
    #
    vy
    cA
    wrex
    #
    @13
    @19
    @20
    @21
    cr
    wcel
    #
    @23
    @8
    peano2re
    #
    @24
    @20
    @23
    @24
    @5
    @23
    @0
    @4
    @23
    vx
    @21
    cr
    @1
    @21
    wceq
    @3
    @22
    vy
    cA
    @1
    @21
    @2
    cle
    breq1
    rexbidv
    rspcva
    adantrr
    ancoms
    sylan2
    @0
    @19
    @23
    @13
    wi
    @5
    @0
    @19
    wa
    @22
    @12
    vy
    cA
    @0
    @2
    cA
    wcel
    #
    @19
    @22
    @12
    wi
    #
    @0
    @26
    wa
    @2
    cxr
    wcel
    #
    @19
    @27
    cA
    cxr
    @2
    ssel2
    #
    @19
    @28
    @27
    @19
    @28
    wa
    @8
    @21
    clt
    wbr
    #
    @22
    @12
    @19
    @30
    @28
    @8
    ltp1
    adantr
    @19
    @19
    @24
    wa
    @28
    @30
    @22
    wa
    @12
    wi
    #
    @19
    @24
    @25
    ancli
    @19
    @24
    @28
    @31
    @19
    @18
    @24
    @28
    @31
    @8
    rexr
    @24
    @18
    @21
    cxr
    wcel
    @28
    @31
    @21
    rexr
    @8
    @21
    @2
    xrltletr
    syl3an2
    syl3an1
    3expa
    sylan
    mpand
    ancoms
    sylan
    an32s
    reximdva
    adantll
    mpd
    exp31
    a1dd
    com4r
    com13
    imp
    ralrimiv
    jca
    @0
    cpnf
    cxr
    wcel
    @16
    @7
    pnfxr
    vz
    vy
    cA
    cpnf
    supxr
    mpanl2
    syldan
    ex
    @0
    @7
    @4
    vx
    cr
    @0
    @1
    cr
    wcel
    #
    wa
    #
    @7
    @1
    @2
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    @4
    @33
    @7
    @35
    @33
    @7
    wa
    #
    @1
    cxr
    wcel
    #
    @1
    @6
    clt
    wbr
    #
    @35
    @32
    @37
    @0
    @7
    @1
    rexr
    #
    ad2antlr
    @32
    @7
    @38
    @0
    @7
    @32
    @38
    @32
    @38
    @7
    @1
    cpnf
    clt
    wbr
    @1
    ltpnf
    @6
    cpnf
    @1
    clt
    breq2
    syl5ibr
    impcom
    adantll
    @36
    vz
    vw
    vy
    cxr
    cA
    @1
    clt
    cxr
    clt
    wor
    @36
    xrltso
    a1i
    @0
    @8
    vw
    cv
    #
    clt
    wbr
    wn
    vw
    cA
    wral
    @40
    @8
    clt
    wbr
    @40
    @2
    clt
    wbr
    vy
    cA
    wrex
    wi
    vw
    cxr
    wral
    wa
    vz
    cxr
    wrex
    @32
    @7
    vz
    vw
    vy
    cA
    xrsupss
    ad2antrr
    suplub
    mp2and
    ex
    @33
    @34
    @3
    vy
    cA
    @33
    @26
    wa
    @37
    @28
    @34
    @3
    wi
    @32
    @37
    @0
    @26
    @39
    ad2antlr
    @0
    @26
    @28
    @32
    @29
    adantlr
    @1
    @2
    xrltle
    syl2anc
    reximdva
    syld
    ralrimdva
    impbid
end
