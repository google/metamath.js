include "crn.mm"
include "wf1o.mm"
include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "csn.mm"
include "wcel.mm"
include "wsbc.mm"
include "eqid.mm"
include "cvv.mm"
include "wb.mm"
include "snex.mm"
include "eqsbc3.mm"
include "ax-mp.mm"
include "mpbir.mm"
include "csb.mm"
include "sbcel2.mm"
include "csbconstg.mm"
include "eleq2i.mm"
include "bitri.mm"
include "wa.mm"
include "wrex.mm"
include "wex.mm"
include "abeq2i.mm"
include "df-rex.mm"
include "sylbbr.mm"
include "19.23bi.mm"
include "sbcth.mm"
include "sbcimg.mm"
include "mpbi.mm"
include "sbcan.mm"
include "sbcel1v.mm"
include "3imtr3i.mm"
include "sylanbr.mm"
include "mpan2.mm"
include "fmpti.mm"
include "fvmpt2.mm"
include "mpdan.mm"
include "sneq.mm"
include "fvmpt3i.mm"
include "eqeqan12d.mm"
include "vex.mm"
include "sneqbg.mm"
include "syl6bb.mm"
include "biimpd.mm"
include "rgen2a.mm"
include "dff13.mm"
include "mpbir2an.mm"
include "f1f1orn.mm"
include "cmpt.mm"
include "cab.mm"
include "rnmptsn.mm"
include "rneqi.mm"
include "3eqtr4i.mm"
include "f1oeq3.mm"

theorem f1omptsnlem
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cR: class R
  let cF: class F
  let vy: setvar y
  assume f1omptsn.f: |- F = ( x e. A |-> { x } )
  assume f1omptsn.r: |- R = { u | E. x e. A u = { x } }

  disjoint A x
  disjoint A u
  disjoint u x
  disjoint F x
  disjoint R u
  disjoint R x
  disjoint A y
  disjoint x y
  disjoint F y
  assert |- F : A -1-1-onto-> R

  proof
    cA
    cF
    crn
    #
    cF
    wf1o
    #
    cA
    cR
    cF
    wf1o
    #
    cA
    cR
    cF
    wf1
    #
    @1
    @3
    cA
    cR
    cF
    wf
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @4
    @6
    wceq
    #
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    vx
    cA
    cR
    @4
    csn
    #
    cF
    f1omptsn.f
    @4
    cA
    wcel
    #
    vu
    cv
    #
    @11
    wceq
    #
    vu
    @11
    wsbc
    #
    @11
    cR
    wcel
    #
    @15
    @11
    @11
    wceq
    #
    @11
    eqid
    @11
    cvv
    wcel
    #
    @15
    @17
    wb
    @4
    snex
    #
    vu
    @11
    @11
    cvv
    eqsbc3
    ax-mp
    mpbir
    @12
    @12
    vu
    @11
    wsbc
    #
    @15
    @16
    @20
    @4
    vu
    @11
    cA
    csb
    #
    wcel
    @12
    vu
    @11
    @4
    cA
    sbcel2
    @21
    cA
    @4
    @18
    @21
    cA
    wceq
    @19
    vu
    @11
    cA
    cvv
    csbconstg
    ax-mp
    eleq2i
    bitri
    @12
    @14
    wa
    #
    vu
    @11
    wsbc
    #
    @13
    cR
    wcel
    #
    vu
    @11
    wsbc
    #
    @20
    @15
    wa
    @16
    @22
    @24
    wi
    #
    vu
    @11
    wsbc
    #
    @23
    @25
    wi
    #
    @18
    @27
    @19
    @26
    vu
    @11
    cvv
    @22
    @24
    vx
    @24
    @14
    vx
    cA
    wrex
    #
    @22
    vx
    wex
    @29
    vu
    cR
    f1omptsn.r
    abeq2i
    @14
    vx
    cA
    df-rex
    sylbbr
    19.23bi
    sbcth
    ax-mp
    @18
    @27
    @28
    wb
    @19
    @22
    @24
    vu
    @11
    cvv
    sbcimg
    ax-mp
    mpbi
    @12
    @14
    vu
    @11
    sbcan
    vu
    @11
    cR
    sbcel1v
    3imtr3i
    sylanbr
    mpan2
    #
    fmpti
    @10
    vx
    vy
    cA
    @12
    @6
    cA
    wcel
    #
    wa
    #
    @8
    @9
    @32
    @8
    @11
    @6
    csn
    #
    wceq
    #
    @9
    @12
    @31
    @5
    @11
    @7
    @33
    @12
    @16
    @5
    @11
    wceq
    @30
    vx
    cA
    @11
    cR
    cF
    f1omptsn.f
    fvmpt2
    mpdan
    vx
    @6
    @11
    @33
    cA
    cF
    @4
    @6
    sneq
    f1omptsn.f
    @19
    fvmpt3i
    eqeqan12d
    @4
    cvv
    wcel
    @34
    @9
    wb
    vx
    vex
    @4
    @6
    cvv
    sneqbg
    ax-mp
    syl6bb
    biimpd
    rgen2a
    vx
    vy
    cA
    cR
    cF
    dff13
    mpbir2an
    cA
    cR
    cF
    f1f1orn
    ax-mp
    @0
    cR
    wceq
    @1
    @2
    wb
    vx
    cA
    @11
    cmpt
    #
    crn
    @29
    vu
    cab
    @0
    cR
    vx
    vu
    cA
    rnmptsn
    cF
    @35
    f1omptsn.f
    rneqi
    f1omptsn.r
    3eqtr4i
    @0
    cR
    cA
    cF
    f1oeq3
    ax-mp
    mpbi
end
