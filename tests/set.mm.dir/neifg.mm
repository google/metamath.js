include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "crab.mm"
include "cfg.mm"
include "co.mm"
include "cpw.mm"
include "cin.mm"
include "cnei.mm"
include "cfv.mm"
include "cfbas.mm"
include "wceq.mm"
include "opnfbas.mm"
include "fgval.mm"
include "syl.mm"
include "wa.mm"
include "pweq.mm"
include "ineq2d.mm"
include "neeq1d.mm"
include "elrab.mm"
include "wex.mm"
include "wb.mm"
include "selpw.mm"
include "a1i.mm"
include "n0.mm"
include "elin.mm"
include "sseq2.mm"
include "anbi12i.mm"
include "bitri.mm"
include "exbii.mm"
include "anbi12d.mm"
include "wrex.mm"
include "isnei.mm"
include "3adant3.mm"
include "anass.mm"
include "df-rex.mm"
include "bitr4i.mm"
include "anbi2i.mm"
include "syl6rbbr.mm"
include "bitrd.mm"
include "syl5bb.mm"
include "eqrdv.mm"
include "eqtrd.mm"

theorem neifg
  let vx: setvar x
  let cS: class S
  let cJ: class J
  let cX: class X
  let vt: setvar t
  let vu: setvar u
  let vz: setvar z
  assume neifg.1: |- X = U. J

  disjoint J x
  disjoint S x
  disjoint X x
  disjoint t u
  disjoint t x
  disjoint t z
  disjoint J t
  disjoint u x
  disjoint u z
  disjoint J u
  disjoint x z
  disjoint J z
  disjoint S t
  disjoint S u
  disjoint S z
  disjoint X t
  disjoint X u
  disjoint X z
  assert |- ( ( J e. Top /\ S C_ X /\ S =/= (/) ) -> ( X filGen { x e. J | S C_ x } ) = ( ( nei ` J ) ` S ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    cS
    c0
    wne
    #
    w3a
    #
    cX
    cS
    vx
    cv
    #
    wss
    #
    vx
    cJ
    crab
    #
    cfg
    co
    #
    @6
    vt
    cv
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    vt
    cX
    cpw
    #
    crab
    #
    cS
    cJ
    cnei
    cfv
    cfv
    #
    @3
    @6
    cX
    cfbas
    cfv
    wcel
    @7
    @13
    wceq
    vx
    cS
    cJ
    cX
    neifg.1
    opnfbas
    vt
    @6
    cX
    fgval
    syl
    @3
    vu
    @13
    @14
    vu
    cv
    #
    @13
    wcel
    @15
    @12
    wcel
    #
    @6
    @15
    cpw
    #
    cin
    #
    c0
    wne
    #
    wa
    #
    @3
    @15
    @14
    wcel
    #
    @11
    @19
    vt
    @15
    @12
    @8
    @15
    wceq
    #
    @10
    @18
    c0
    @22
    @9
    @17
    @6
    @8
    @15
    pweq
    ineq2d
    neeq1d
    elrab
    @3
    @20
    @15
    cX
    wss
    #
    vz
    cv
    #
    cJ
    wcel
    #
    cS
    @24
    wss
    #
    wa
    #
    @24
    @15
    wss
    #
    wa
    #
    vz
    wex
    #
    wa
    #
    @21
    @3
    @16
    @23
    @19
    @30
    @16
    @23
    wb
    @3
    vu
    cX
    selpw
    a1i
    @19
    @30
    wb
    @3
    @19
    @24
    @18
    wcel
    #
    vz
    wex
    @30
    vz
    @18
    n0
    @32
    @29
    vz
    @32
    @24
    @6
    wcel
    #
    @24
    @17
    wcel
    #
    wa
    @29
    @24
    @6
    @17
    elin
    @33
    @27
    @34
    @28
    @5
    @26
    vx
    @24
    cJ
    @4
    @24
    cS
    sseq2
    elrab
    vz
    @15
    selpw
    anbi12i
    bitri
    exbii
    bitri
    a1i
    anbi12d
    @3
    @21
    @23
    @26
    @28
    wa
    #
    vz
    cJ
    wrex
    #
    wa
    #
    @31
    @0
    @1
    @21
    @37
    wb
    @2
    cS
    vz
    cJ
    @15
    cX
    neifg.1
    isnei
    3adant3
    @30
    @36
    @23
    @30
    @25
    @35
    wa
    #
    vz
    wex
    @36
    @29
    @38
    vz
    @25
    @26
    @28
    anass
    exbii
    @35
    vz
    cJ
    df-rex
    bitr4i
    anbi2i
    syl6rbbr
    bitrd
    syl5bb
    eqrdv
    eqtrd
end
