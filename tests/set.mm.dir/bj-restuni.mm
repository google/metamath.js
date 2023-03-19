include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cuni.mm"
include "cin.mm"
include "cv.mm"
include "wex.mm"
include "eluni.mm"
include "wceq.mm"
include "wrex.mm"
include "elrest.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "wb.mm"
include "bicomi.mm"
include "anbi1i.mm"
include "a1i.mm"
include "df-rex.mm"
include "anbi2i.mm"
include "19.42v.mm"
include "bitri.mm"
include "exbii.mm"
include "excom.mm"
include "an12.mm"
include "eqimss.mm"
include "sseld.mm"
include "imdistanri.mm"
include "eqimss2.mm"
include "impbii.mm"
include "vex.mm"
include "inex1.mm"
include "isseti.mm"
include "biantru.mm"
include "elin.mm"
include "3bitri.mm"
include "biid.mm"
include "bianass.mm"
include "ancom.mm"
include "19.41v.mm"
include "3bitr4g.mm"
include "bitrd.mm"
include "syl5bb.mm"
include "eqrdv.mm"

theorem bj-restuni
  let cA: class A
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( X e. V /\ A e. W ) -> U. ( X |`t A ) = ( U. X i^i A ) )

  proof
    cX
    cV
    wcel
    cA
    cW
    wcel
    wa
    #
    vx
    cX
    cA
    crest
    co
    #
    cuni
    #
    cX
    cuni
    #
    cA
    cin
    #
    vx
    cv
    #
    @2
    wcel
    @5
    vy
    cv
    #
    wcel
    #
    @6
    @1
    wcel
    #
    wa
    #
    vy
    wex
    #
    @0
    @5
    @4
    wcel
    #
    vy
    @5
    @1
    eluni
    @0
    @10
    @7
    @6
    vz
    cv
    #
    cA
    cin
    #
    wceq
    #
    vz
    cX
    wrex
    #
    wa
    #
    vy
    wex
    #
    @11
    @0
    @9
    @16
    vy
    @0
    @8
    @15
    @7
    vz
    @6
    cA
    cX
    cV
    cW
    elrest
    anbi2d
    exbidv
    @0
    @5
    @12
    wcel
    #
    @12
    cX
    wcel
    #
    wa
    #
    vz
    wex
    #
    @5
    cA
    wcel
    #
    wa
    #
    @5
    @3
    wcel
    #
    @22
    wa
    #
    @17
    @11
    @23
    @25
    wb
    @0
    @21
    @24
    @22
    @24
    @21
    vz
    @5
    cX
    eluni
    bicomi
    anbi1i
    a1i
    @17
    @7
    @19
    @14
    wa
    #
    wa
    #
    vz
    wex
    #
    vy
    wex
    @27
    vy
    wex
    #
    vz
    wex
    #
    @23
    @16
    @28
    vy
    @16
    @7
    @26
    vz
    wex
    #
    wa
    #
    @28
    @15
    @31
    @7
    @14
    vz
    cX
    df-rex
    anbi2i
    @28
    @32
    @7
    @26
    vz
    19.42v
    bicomi
    bitri
    exbii
    @27
    vy
    vz
    excom
    @30
    @20
    @22
    wa
    #
    vz
    wex
    @23
    @29
    @33
    vz
    @29
    @19
    @7
    @14
    wa
    #
    wa
    #
    vy
    wex
    @19
    @34
    vy
    wex
    #
    wa
    #
    @33
    @27
    @35
    vy
    @7
    @19
    @14
    an12
    exbii
    @19
    @34
    vy
    19.42v
    @37
    @19
    @18
    @22
    wa
    #
    wa
    @19
    @18
    wa
    #
    @22
    wa
    @33
    @36
    @38
    @19
    @36
    @5
    @13
    wcel
    #
    @14
    wa
    #
    vy
    wex
    @40
    @14
    vy
    wex
    #
    wa
    #
    @38
    @34
    @41
    vy
    @34
    @41
    @14
    @7
    @40
    @14
    @6
    @13
    @5
    @6
    @13
    eqimss
    sseld
    imdistanri
    @14
    @40
    @7
    @14
    @13
    @6
    @5
    @13
    @6
    eqimss2
    sseld
    imdistanri
    impbii
    exbii
    @40
    @14
    vy
    19.42v
    @43
    @40
    @38
    @40
    @43
    @42
    @40
    vy
    @13
    @12
    cA
    vz
    vex
    inex1
    isseti
    biantru
    bicomi
    @5
    @12
    cA
    elin
    bitri
    3bitri
    anbi2i
    @38
    @18
    @22
    @19
    @38
    biid
    bianass
    @39
    @20
    @22
    @19
    @18
    ancom
    anbi1i
    3bitri
    3bitri
    exbii
    @20
    @22
    vz
    19.41v
    bitri
    3bitri
    @5
    @3
    cA
    elin
    3bitr4g
    bitrd
    syl5bb
    eqrdv
end
