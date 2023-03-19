include "cxr.mm"
include "wss.mm"
include "cr.mm"
include "cpnf.mm"
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
include "cmnf.mm"
include "xrsupsslem.mm"
include "csn.mm"
include "cdif.mm"
include "ssdifss.mm"
include "w3o.mm"
include "ssxr.mm"
include "df-3or.mm"
include "neldifsn.mm"
include "biorfi.mm"
include "bitr4i.mm"
include "sylib.mm"
include "mpdan.mm"
include "syl.mm"
include "cun.mm"
include "xrsupexmnf.mm"
include "wb.mm"
include "snssi.mm"
include "wceq.mm"
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
include "mpjaodan.mm"

theorem xrsupss
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
  assert |- ( A C_ RR* -> E. x e. RR* ( A. y e. A -. x < y /\ A. y e. RR* ( y < x -> E. z e. A y < z ) ) )

  proof
    cA
    cxr
    wss
    #
    cA
    cr
    wss
    #
    cpnf
    cA
    wcel
    #
    wo
    #
    vx
    cv
    #
    vy
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
    @5
    vz
    cv
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
    cmnf
    cA
    wcel
    #
    vx
    vy
    vz
    cA
    xrsupsslem
    @0
    @6
    vy
    cA
    cmnf
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
    cpnf
    @17
    wcel
    #
    wo
    #
    @18
    @19
    @20
    @21
    cmnf
    @17
    wcel
    #
    w3o
    #
    @22
    @17
    ssxr
    @24
    @22
    @23
    wo
    @22
    @20
    @21
    @23
    df-3or
    @23
    @22
    cmnf
    cA
    neldifsn
    biorfi
    bitr4i
    sylib
    vx
    vy
    vz
    @17
    xrsupsslem
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
    @25
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
    xrsupexmnf
    @15
    @30
    @13
    vx
    cxr
    @15
    @16
    cA
    wss
    #
    @30
    @13
    wb
    #
    cmnf
    cA
    snssi
    @31
    @25
    cA
    wceq
    #
    @32
    @31
    @16
    @17
    cun
    #
    cA
    wceq
    @33
    @16
    cA
    undif
    @34
    @25
    cA
    @16
    @17
    uncom
    eqeq1i
    bitri
    @33
    @26
    @7
    @29
    @12
    @6
    vy
    @25
    cA
    raleq
    @33
    @28
    @11
    vy
    cxr
    @33
    @27
    @10
    @8
    @9
    vz
    @25
    cA
    rexeq
    imbi2d
    ralbidv
    anbi12d
    sylbi
    syl
    rexbidv
    syl5ib
    mpan9
    @0
    @1
    @2
    @15
    w3o
    @3
    @15
    wo
    cA
    ssxr
    @1
    @2
    @15
    df-3or
    sylib
    mpjaodan
end
