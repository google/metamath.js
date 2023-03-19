include "cv.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cz.mm"
include "crab.mm"
include "wf1o.mm"
include "wf1.mm"
include "crn.mm"
include "wf.mm"
include "cfv.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "cfz.mm"
include "elfzelz.mm"
include "eleq2s.mm"
include "2z.mm"
include "a1i.mm"
include "zmulcld.mm"
include "id.mm"
include "wb.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "eqidd.mm"
include "rspcedvd.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "fmpti.mm"
include "wa.mm"
include "cvv.mm"
include "cmpt.mm"
include "simpl.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "simpr.mm"
include "eqeq12d.mm"
include "cc.mm"
include "zcnd.mm"
include "adantr.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "mulcan2d.mm"
include "biimpd.mm"
include "sylbid.mm"
include "rgen2.mm"
include "dff13.mm"
include "mpbir2an.mm"
include "cab.mm"
include "cbvrexv.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "pm4.71ri.mm"
include "bitri.mm"
include "abbii.mm"
include "rnmpt.mm"
include "df-rab.mm"
include "3eqtr4i.mm"
include "dff1o5.mm"

theorem 2lgslem1b
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cI: class I
  let vy: setvar y
  let vz: setvar z
  assume 2lgslem1b.i: |- I = ( A ... B )
  assume 2lgslem1b.f: |- F = ( j e. I |-> ( j x. 2 ) )

  disjoint I i
  disjoint I j
  disjoint I x
  disjoint i j
  disjoint i x
  disjoint j x
  disjoint F y
  disjoint F z
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint i y
  disjoint i z
  disjoint j y
  disjoint j z
  disjoint x y
  disjoint x z
  assert |- F : I -1-1-onto-> { x e. ZZ | E. i e. I x = ( i x. 2 ) }

  proof
    cI
    vx
    cv
    #
    vi
    cv
    #
    c2
    cmul
    co
    #
    wceq
    #
    vi
    cI
    wrex
    #
    vx
    cz
    crab
    #
    cF
    wf1o
    cI
    @5
    cF
    wf1
    #
    cF
    crn
    #
    @5
    wceq
    @6
    cI
    @5
    cF
    wf
    vy
    cv
    #
    cF
    cfv
    #
    vz
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vy
    vz
    weq
    #
    wi
    #
    vz
    cI
    wral
    vy
    cI
    wral
    vj
    cI
    @5
    vj
    cv
    #
    c2
    cmul
    co
    #
    cF
    2lgslem1b.f
    @15
    cI
    wcel
    #
    @16
    cz
    wcel
    @16
    @2
    wceq
    #
    vi
    cI
    wrex
    #
    @16
    @5
    wcel
    @17
    @15
    c2
    @15
    cz
    wcel
    @15
    cA
    cB
    cfz
    co
    #
    cI
    @15
    cA
    cB
    elfzelz
    2lgslem1b.i
    eleq2s
    c2
    cz
    wcel
    #
    @17
    2z
    a1i
    zmulcld
    @17
    @18
    @16
    @16
    wceq
    #
    vi
    @15
    cI
    @17
    id
    vi
    vj
    weq
    #
    @18
    @22
    wb
    @17
    @23
    @2
    @16
    @16
    @1
    @15
    c2
    cmul
    oveq1
    eqeq2d
    adantl
    @17
    @16
    eqidd
    rspcedvd
    @4
    @19
    vx
    @16
    cz
    @0
    @16
    wceq
    #
    @3
    @18
    vi
    cI
    @0
    @16
    @2
    eqeq1
    rexbidv
    elrab
    sylanbrc
    fmpti
    @14
    vy
    vz
    cI
    cI
    @8
    cI
    wcel
    #
    @10
    cI
    wcel
    #
    wa
    #
    @12
    @8
    c2
    cmul
    co
    #
    @10
    c2
    cmul
    co
    #
    wceq
    #
    @13
    @27
    @9
    @28
    @11
    @29
    @27
    vj
    @8
    @16
    @28
    cI
    cF
    cvv
    cF
    vj
    cI
    @16
    cmpt
    wceq
    @27
    2lgslem1b.f
    a1i
    #
    vj
    vy
    weq
    @16
    @28
    wceq
    @27
    @15
    @8
    c2
    cmul
    oveq1
    adantl
    @25
    @26
    simpl
    @27
    @8
    c2
    cmul
    ovexd
    fvmptd
    @27
    vj
    @10
    @16
    @29
    cI
    cF
    cvv
    @31
    vj
    vz
    weq
    @16
    @29
    wceq
    @27
    @15
    @10
    c2
    cmul
    oveq1
    adantl
    @25
    @26
    simpr
    @27
    @10
    c2
    cmul
    ovexd
    fvmptd
    eqeq12d
    @27
    @30
    @13
    @27
    @8
    @10
    c2
    @25
    @8
    cc
    wcel
    @26
    @25
    @8
    @8
    cz
    wcel
    @8
    @20
    cI
    @8
    cA
    cB
    elfzelz
    2lgslem1b.i
    eleq2s
    zcnd
    adantr
    @26
    @10
    cc
    wcel
    @25
    @26
    @10
    @10
    cz
    wcel
    @10
    @20
    cI
    @10
    cA
    cB
    elfzelz
    2lgslem1b.i
    eleq2s
    zcnd
    adantl
    @27
    2cnd
    c2
    cc0
    wne
    @27
    2ne0
    a1i
    mulcan2d
    biimpd
    sylbid
    rgen2
    vy
    vz
    cI
    @5
    cF
    dff13
    mpbir2an
    @24
    vj
    cI
    wrex
    #
    vx
    cab
    @0
    cz
    wcel
    #
    @4
    wa
    #
    vx
    cab
    @7
    @5
    @32
    @34
    vx
    @32
    @4
    @34
    @24
    @3
    vj
    vi
    cI
    vj
    vi
    weq
    @16
    @2
    @0
    @15
    @1
    c2
    cmul
    oveq1
    eqeq2d
    cbvrexv
    @4
    @33
    @3
    @33
    vi
    cI
    @1
    cI
    wcel
    @33
    @3
    @2
    cz
    wcel
    #
    @35
    @1
    @20
    cI
    @1
    @20
    wcel
    #
    @1
    c2
    @1
    cA
    cB
    elfzelz
    @21
    @36
    2z
    a1i
    zmulcld
    2lgslem1b.i
    eleq2s
    @0
    @2
    cz
    eleq1
    syl5ibrcom
    rexlimiv
    pm4.71ri
    bitri
    abbii
    vj
    vx
    cI
    @16
    cF
    2lgslem1b.f
    rnmpt
    @4
    vx
    cz
    df-rab
    3eqtr4i
    cI
    @5
    cF
    dff1o5
    mpbir2an
end
