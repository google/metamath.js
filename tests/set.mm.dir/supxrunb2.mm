include "cxr.mm"
include "wss.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "cr.mm"
include "wral.mm"
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
include "breq1.mm"
include "rexbidv.mm"
include "rspcva.mm"
include "adantrr.mm"
include "ancoms.mm"
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
include "rexr.mm"
include "ad2antlr.mm"
include "ltpnf.mm"
include "breq2.mm"
include "syl5ibr.mm"
include "impcom.mm"
include "adantll.mm"
include "wor.mm"
include "xrltso.mm"
include "a1i.mm"
include "xrsupss.mm"
include "ad2antrr.mm"
include "suplub.mm"
include "mp2and.mm"
include "com23.mm"
include "ralrimdv.mm"
include "impbid.mm"

theorem supxrunb2
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
  assert |- ( A C_ RR* -> ( A. x e. RR E. y e. A x < y <-> sup ( A , RR* , < ) = +oo ) )

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
    clt
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
    @18
    @5
    @0
    @14
    @5
    @0
    @11
    @18
    @13
    @5
    @0
    @18
    @13
    wi
    @11
    @5
    @0
    @18
    @13
    @18
    @5
    @0
    wa
    @13
    @18
    @5
    @13
    @0
    @4
    @13
    vx
    @8
    cr
    @1
    @8
    wceq
    @3
    @12
    vy
    cA
    @1
    @8
    @2
    clt
    breq1
    rexbidv
    rspcva
    adantrr
    ancoms
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
    @7
    @4
    @0
    @19
    @7
    @4
    @0
    @19
    wa
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
    @4
    @19
    @21
    @0
    @7
    @1
    rexr
    ad2antlr
    @19
    @7
    @22
    @0
    @7
    @19
    @22
    @19
    @22
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
    @20
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
    @20
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
    @23
    @8
    clt
    wbr
    @23
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
    @19
    @7
    vz
    vw
    vy
    cA
    xrsupss
    ad2antrr
    suplub
    mp2and
    exp31
    com23
    ralrimdv
    impbid
end
