include "cxr.mm"
include "wss.mm"
include "cr.mm"
include "cmnf.mm"
include "wcel.mm"
include "wo.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "cpnf.mm"
include "xrinfmsslem.mm"
include "csn.mm"
include "cdif.mm"
include "ssdifss.mm"
include "w3o.mm"
include "ssxr.mm"
include "3orass.mm"
include "wb.mm"
include "pnfex.mm"
include "snid.mm"
include "elndif.mm"
include "biorf.mm"
include "mp2b.mm"
include "orbi2i.mm"
include "bitr4i.mm"
include "sylib.mm"
include "mpdan.mm"
include "syl.mm"
include "cun.mm"
include "xrinfmexpnf.mm"
include "wceq.mm"
include "snss.mm"
include "undif.mm"
include "uncom.mm"
include "eqeq1i.mm"
include "bitri.mm"
include "raleq.mm"
include "rexeq.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "sylbi.mm"
include "rexbidv.mm"
include "syl5ib.mm"
include "mpan9.mm"
include "df-3or.mm"
include "or32.mm"
include "mpjaodan.mm"

theorem xrinfmss
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w
  let cB: class B

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B w
  assert |- ( A C_ RR* -> E. x e. RR* ( A. y e. A -. y < x /\ A. y e. RR* ( x < y -> E. z e. A z < y ) ) )

  proof
    cA
    cxr
    wss
    #
    cA
    cr
    wss
    #
    cmnf
    cA
    wcel
    #
    wo
    #
    vy
    cv
    #
    vx
    cv
    #
    clt
    wbr
    wn
    #
    vy
    cA
    wral
    #
    @5
    @4
    clt
    wbr
    #
    vz
    cv
    @4
    clt
    wbr
    #
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cxr
    wral
    #
    wa
    #
    vx
    cxr
    wrex
    #
    cpnf
    cA
    wcel
    #
    vx
    vy
    vz
    cA
    xrinfmsslem
    @0
    @6
    vy
    cA
    cpnf
    csn
    #
    cdif
    #
    wral
    @8
    @9
    vz
    @17
    wrex
    wi
    vy
    cxr
    wral
    wa
    vx
    cxr
    wrex
    #
    @15
    @14
    @0
    @17
    cxr
    wss
    #
    @18
    cA
    cxr
    @16
    ssdifss
    @19
    @17
    cr
    wss
    #
    cmnf
    @17
    wcel
    #
    wo
    #
    @18
    @19
    @20
    cpnf
    @17
    wcel
    #
    @21
    w3o
    #
    @22
    @17
    ssxr
    @24
    @20
    @23
    @21
    wo
    #
    wo
    @22
    @20
    @23
    @21
    3orass
    @21
    @25
    @20
    cpnf
    @16
    wcel
    @23
    wn
    @21
    @25
    wb
    cpnf
    pnfex
    snid
    cpnf
    @16
    cA
    elndif
    @23
    @21
    biorf
    mp2b
    orbi2i
    bitr4i
    sylib
    vx
    vy
    vz
    @17
    xrinfmsslem
    mpdan
    syl
    @18
    @6
    vy
    @17
    @16
    cun
    #
    wral
    #
    @8
    @9
    vz
    @26
    wrex
    #
    wi
    #
    vy
    cxr
    wral
    #
    wa
    #
    vx
    cxr
    wrex
    @15
    @14
    vx
    vy
    vz
    @17
    xrinfmexpnf
    @15
    @31
    @13
    vx
    cxr
    @15
    @26
    cA
    wceq
    #
    @31
    @13
    wb
    @15
    @16
    cA
    wss
    #
    @32
    cpnf
    cA
    pnfex
    snss
    @33
    @16
    @17
    cun
    #
    cA
    wceq
    @32
    @16
    cA
    undif
    @34
    @26
    cA
    @16
    @17
    uncom
    eqeq1i
    bitri
    bitri
    @32
    @27
    @7
    @30
    @12
    @6
    vy
    @26
    cA
    raleq
    @32
    @29
    @11
    vy
    cxr
    @32
    @28
    @10
    @8
    @9
    vz
    @26
    cA
    rexeq
    imbi2d
    ralbidv
    anbi12d
    sylbi
    rexbidv
    syl5ib
    mpan9
    @0
    @1
    @15
    @2
    w3o
    #
    @3
    @15
    wo
    #
    cA
    ssxr
    @35
    @1
    @15
    wo
    @2
    wo
    @36
    @1
    @15
    @2
    df-3or
    @1
    @15
    @2
    or32
    bitri
    sylib
    mpjaodan
end
