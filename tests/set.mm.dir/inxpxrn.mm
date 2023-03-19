include "cxp.mm"
include "cin.mm"
include "cxrn.mm"
include "xrnrel.mm"
include "relinxp.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "cop.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "wb.mm"
include "cvv.mm"
include "brxrn2.mm"
include "elv.mm"
include "anbi2i.mm"
include "xrninxp2.mm"
include "brabidga.mm"
include "3anass.mm"
include "2exbii.mm"
include "brinxp2ALTV.mm"
include "anbi12i.mm"
include "anan.mm"
include "bitri.mm"
include "anass.mm"
include "eqelb.mm"
include "opelxp.mm"
include "bitr2i.mm"
include "anbi1i.mm"
include "3bitr2i.mm"
include "ancom.mm"
include "3bitri.mm"
include "an12.mm"
include "bitr4i.mm"
include "19.42vv.mm"
include "3bitr4ri.mm"
include "eqbrriv.mm"

theorem inxpxrn
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( R i^i ( A X. B ) ) |X. ( S i^i ( A X. C ) ) ) = ( ( R |X. S ) i^i ( A X. ( B X. C ) ) )

  proof
    vu
    vx
    cR
    cA
    cB
    cxp
    cin
    #
    cS
    cA
    cC
    cxp
    cin
    #
    cxrn
    #
    cR
    cS
    cxrn
    #
    cA
    cB
    cC
    cxp
    #
    cxp
    cin
    #
    @0
    @1
    xrnrel
    cA
    @4
    @3
    relinxp
    vx
    cv
    #
    @4
    wcel
    #
    vu
    cv
    #
    cA
    wcel
    #
    @8
    @6
    @3
    wbr
    #
    wa
    #
    wa
    #
    @7
    @9
    @6
    vy
    cv
    #
    vz
    cv
    #
    cop
    #
    wceq
    #
    @8
    @13
    cR
    wbr
    #
    @8
    @14
    cS
    wbr
    #
    w3a
    #
    vz
    wex
    vy
    wex
    #
    wa
    #
    wa
    #
    @8
    @6
    @5
    wbr
    @8
    @6
    @2
    wbr
    #
    @11
    @21
    @7
    @10
    @20
    @9
    @10
    @20
    wb
    vu
    vy
    vz
    @8
    @6
    cR
    cS
    cvv
    brxrn2
    elv
    anbi2i
    anbi2i
    @12
    vu
    vx
    @5
    vx
    vu
    cA
    cB
    cC
    cR
    cS
    xrninxp2
    brabidga
    @23
    @16
    @8
    @13
    @0
    wbr
    #
    @8
    @14
    @1
    wbr
    #
    w3a
    #
    vz
    wex
    vy
    wex
    #
    @16
    @24
    @25
    wa
    #
    wa
    #
    vz
    wex
    vy
    wex
    #
    @22
    @23
    @27
    wb
    vu
    vy
    vz
    @8
    @6
    @0
    @1
    cvv
    brxrn2
    elv
    @26
    @29
    vy
    vz
    @16
    @24
    @25
    3anass
    2exbii
    @30
    @7
    @9
    @19
    wa
    #
    wa
    #
    vz
    wex
    vy
    wex
    @7
    @31
    vz
    wex
    vy
    wex
    #
    wa
    @22
    @29
    @32
    vy
    vz
    @29
    @7
    @16
    @9
    @17
    @18
    wa
    #
    wa
    #
    wa
    #
    wa
    #
    @32
    @29
    @16
    @7
    wa
    #
    @35
    wa
    #
    @7
    @16
    wa
    #
    @35
    wa
    @37
    @29
    @16
    @13
    cB
    wcel
    #
    @14
    cC
    wcel
    #
    wa
    #
    @35
    wa
    #
    wa
    @16
    @43
    wa
    #
    @35
    wa
    @39
    @28
    @44
    @16
    @28
    @9
    @41
    wa
    @17
    wa
    #
    @9
    @42
    wa
    @18
    wa
    #
    wa
    @44
    @24
    @46
    @25
    @47
    cA
    cB
    @8
    @13
    cR
    brinxp2ALTV
    cA
    cC
    @8
    @14
    cS
    brinxp2ALTV
    anbi12i
    @9
    @41
    @17
    @42
    @18
    anan
    bitri
    anbi2i
    @16
    @43
    @35
    anass
    @45
    @38
    @35
    @38
    @16
    @15
    @4
    wcel
    #
    wa
    @45
    @6
    @15
    @4
    eqelb
    @48
    @43
    @16
    @13
    @14
    cB
    cC
    opelxp
    anbi2i
    bitr2i
    anbi1i
    3bitr2i
    @38
    @40
    @35
    @16
    @7
    ancom
    anbi1i
    @7
    @16
    @35
    anass
    3bitri
    @36
    @31
    @7
    @36
    @9
    @16
    @34
    wa
    #
    wa
    @31
    @16
    @9
    @34
    an12
    @19
    @49
    @9
    @16
    @17
    @18
    3anass
    anbi2i
    bitr4i
    anbi2i
    bitri
    2exbii
    @7
    @31
    vy
    vz
    19.42vv
    @33
    @21
    @7
    @9
    @19
    vy
    vz
    19.42vv
    anbi2i
    3bitri
    3bitri
    3bitr4ri
    eqbrriv
end
