include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "suprcl.mm"
include "leidd.mm"
include "wcel.mm"
include "wb.mm"
include "suprleub.mm"
include "mpdan.mm"
include "simp1.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "rexrd.mm"
include "supxrleub.mm"
include "syl2anc.mm"
include "bitr4d.mm"
include "mpbid.mm"
include "supxrcl.mm"
include "syl.mm"
include "xrleid.mm"
include "cmnf.mm"
include "wex.mm"
include "simp2.mm"
include "n0.mm"
include "sylib.mm"
include "wa.mm"
include "mnfxr.mm"
include "a1i.mm"
include "sselda.mm"
include "adantr.mm"
include "mnflt.mm"
include "supxrub.mm"
include "sylan.mm"
include "xrltletrd.mm"
include "exlimddv.mm"
include "xrre.mm"
include "syl22anc.mm"
include "xrletri3.mm"
include "mpbir2and.mm"

theorem supxrre
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
  assert |- ( ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A y <_ x ) -> sup ( A , RR* , < ) = sup ( A , RR , < ) )

  proof
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    vy
    cv
    vx
    cv
    #
    cle
    wbr
    vy
    cA
    wral
    vx
    cr
    wrex
    #
    w3a
    #
    cA
    cxr
    clt
    csup
    #
    cA
    cr
    clt
    csup
    #
    wceq
    #
    @5
    @6
    cle
    wbr
    #
    @6
    @5
    cle
    wbr
    #
    @4
    @6
    @6
    cle
    wbr
    #
    @8
    @4
    @6
    vx
    vy
    cA
    suprcl
    #
    leidd
    @4
    @10
    vz
    cv
    #
    @6
    cle
    wbr
    vz
    cA
    wral
    #
    @8
    @4
    @6
    cr
    wcel
    #
    @10
    @13
    wb
    @11
    vx
    vy
    vz
    cA
    @6
    suprleub
    mpdan
    @4
    cA
    cxr
    wss
    #
    @6
    cxr
    wcel
    #
    @8
    @13
    wb
    @4
    cA
    cr
    cxr
    @0
    @1
    @3
    simp1
    #
    ressxr
    syl6ss
    #
    @4
    @6
    @11
    rexrd
    #
    vz
    cA
    @6
    supxrleub
    syl2anc
    bitr4d
    mpbid
    #
    @4
    @5
    @5
    cle
    wbr
    #
    @9
    @4
    @5
    cxr
    wcel
    #
    @21
    @4
    @15
    @22
    @18
    cA
    supxrcl
    syl
    #
    @5
    xrleid
    syl
    @4
    @21
    @2
    @5
    cle
    wbr
    vx
    cA
    wral
    #
    @9
    @4
    @15
    @22
    @21
    @24
    wb
    @18
    @23
    vx
    cA
    @5
    supxrleub
    syl2anc
    @4
    @5
    cr
    wcel
    #
    @9
    @24
    wb
    @4
    @22
    @14
    cmnf
    @5
    clt
    wbr
    #
    @8
    @25
    @23
    @11
    @4
    @12
    cA
    wcel
    #
    @26
    vz
    @4
    @1
    @27
    vz
    wex
    @0
    @1
    @3
    simp2
    vz
    cA
    n0
    sylib
    @4
    @27
    wa
    #
    cmnf
    @12
    @5
    cmnf
    cxr
    wcel
    @28
    mnfxr
    a1i
    @28
    @12
    @4
    cA
    cr
    @12
    @17
    sselda
    #
    rexrd
    @4
    @22
    @27
    @23
    adantr
    @28
    @12
    cr
    wcel
    cmnf
    @12
    clt
    wbr
    @29
    @12
    mnflt
    syl
    @4
    @15
    @27
    @12
    @5
    cle
    wbr
    @18
    cA
    @12
    supxrub
    sylan
    xrltletrd
    exlimddv
    @20
    @5
    @6
    xrre
    syl22anc
    vx
    vy
    vx
    cA
    @5
    suprleub
    mpdan
    bitr4d
    mpbid
    @4
    @22
    @16
    @7
    @8
    @9
    wa
    wb
    @23
    @19
    @5
    @6
    xrletri3
    syl2anc
    mpbir2and
end
