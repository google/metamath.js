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
include "cinf.mm"
include "wcel.mm"
include "simp1.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "infxrcl.mm"
include "syl.mm"
include "infrecl.mm"
include "rexrd.mm"
include "xrleid.mm"
include "wb.mm"
include "infxrgelb.mm"
include "syl2anc.mm"
include "wex.mm"
include "simp2.mm"
include "n0.mm"
include "sylib.mm"
include "wa.mm"
include "cmnf.mm"
include "adantr.mm"
include "sselda.mm"
include "mnfxr.mm"
include "a1i.mm"
include "mnfltd.mm"
include "leidd.mm"
include "infregelb.mm"
include "mpdan.mm"
include "bitr4d.mm"
include "mpbid.mm"
include "xrltletrd.mm"
include "infxrlb.mm"
include "sylan.mm"
include "xrre.mm"
include "syl22anc.mm"
include "exlimddv.mm"
include "xrletrid.mm"

theorem infxrre
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A z
  disjoint x z
  disjoint y z
  assert |- ( ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A x <_ y ) -> inf ( A , RR* , < ) = inf ( A , RR , < ) )

  proof
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
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
    cinf
    #
    cA
    cr
    clt
    cinf
    #
    @4
    cA
    cxr
    wss
    #
    @5
    cxr
    wcel
    #
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
    cA
    infxrcl
    syl
    #
    @4
    @6
    vx
    vy
    cA
    infrecl
    #
    rexrd
    #
    @4
    @5
    @5
    cle
    wbr
    #
    @5
    @6
    cle
    wbr
    #
    @4
    @8
    @14
    @11
    @5
    xrleid
    syl
    @4
    @14
    @5
    @2
    cle
    wbr
    vx
    cA
    wral
    #
    @15
    @4
    @7
    @8
    @14
    @16
    wb
    @10
    @11
    vx
    cA
    @5
    infxrgelb
    syl2anc
    @4
    @5
    cr
    wcel
    #
    @15
    @16
    wb
    @4
    vz
    cv
    #
    cA
    wcel
    #
    @17
    vz
    @4
    @1
    @19
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
    @19
    wa
    @8
    @18
    cr
    wcel
    cmnf
    @5
    clt
    wbr
    #
    @5
    @18
    cle
    wbr
    #
    @17
    @4
    @8
    @19
    @11
    adantr
    @4
    cA
    cr
    @18
    @9
    sselda
    @4
    @20
    @19
    @4
    cmnf
    @6
    @5
    cmnf
    cxr
    wcel
    @4
    mnfxr
    a1i
    @13
    @11
    @4
    @6
    @12
    mnfltd
    @4
    @6
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
    @12
    leidd
    @4
    @22
    @6
    @2
    cle
    wbr
    vx
    cA
    wral
    #
    @23
    @4
    @6
    cr
    wcel
    @22
    @24
    wb
    @12
    vx
    vy
    vx
    cA
    @6
    infregelb
    mpdan
    @4
    @7
    @6
    cxr
    wcel
    @23
    @24
    wb
    @10
    @13
    vx
    cA
    @6
    infxrgelb
    syl2anc
    bitr4d
    mpbid
    #
    xrltletrd
    adantr
    @4
    @7
    @19
    @21
    @10
    cA
    @18
    infxrlb
    sylan
    @5
    @18
    xrre
    syl22anc
    exlimddv
    vx
    vy
    vx
    cA
    @5
    infregelb
    mpdan
    bitr4d
    mpbid
    @25
    xrletrid
end
