include "c0r.mm"
include "cop.mm"
include "cltrr.mm"
include "wbr.mm"
include "cnr.mm"
include "wcel.mm"
include "wa.mm"
include "cltr.mm"
include "cr.mm"
include "ltrelre.mm"
include "brel.mm"
include "opelreal.mm"
include "anbi12i.mm"
include "sylib.mm"
include "ltrelsr.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "wb.mm"
include "opex.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "eqeq1.mm"
include "2exbidv.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "df-lt.mm"
include "brab.mm"
include "baib.mm"
include "vex.mm"
include "eqresr.mm"
include "eqcom.mm"
include "3bitr4i.mm"
include "opth2.mm"
include "bitr4i.mm"
include "anbi1i.mm"
include "2exbii.mm"
include "syl6bb.mm"
include "syl2anbr.mm"
include "breq12.mm"
include "copsex2g.mm"
include "bitrd.mm"
include "pm5.21nii.mm"

theorem ltresr
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( <. A , 0R >. <RR <. B , 0R >. <-> A <R B )

  proof
    cA
    c0r
    cop
    #
    cB
    c0r
    cop
    #
    cltrr
    wbr
    #
    cA
    cnr
    wcel
    #
    cB
    cnr
    wcel
    #
    wa
    #
    cA
    cB
    cltr
    wbr
    #
    @2
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    wa
    #
    @5
    @0
    @1
    cr
    cr
    cltrr
    ltrelre
    brel
    @7
    @3
    @8
    @4
    cA
    opelreal
    #
    cB
    opelreal
    #
    anbi12i
    sylib
    cA
    cB
    cnr
    cnr
    cltr
    ltrelsr
    brel
    @5
    @2
    cA
    cB
    cop
    vz
    cv
    #
    vw
    cv
    #
    cop
    wceq
    #
    @12
    @13
    cltr
    wbr
    #
    wa
    #
    vw
    wex
    vz
    wex
    #
    @6
    @3
    @7
    @8
    @2
    @17
    wb
    @4
    @10
    @11
    @9
    @2
    @0
    @12
    c0r
    cop
    #
    wceq
    #
    @1
    @13
    c0r
    cop
    #
    wceq
    #
    wa
    #
    @15
    wa
    #
    vw
    wex
    vz
    wex
    #
    @17
    @2
    @9
    @24
    vx
    cv
    #
    cr
    wcel
    #
    vy
    cv
    #
    cr
    wcel
    #
    wa
    #
    @25
    @18
    wceq
    #
    @27
    @20
    wceq
    #
    wa
    #
    @15
    wa
    #
    vw
    wex
    vz
    wex
    #
    wa
    @7
    @28
    wa
    #
    @19
    @31
    wa
    #
    @15
    wa
    #
    vw
    wex
    vz
    wex
    #
    wa
    @9
    @24
    wa
    vx
    vy
    @0
    @1
    cltrr
    cA
    c0r
    opex
    cB
    c0r
    opex
    @25
    @0
    wceq
    #
    @29
    @35
    @34
    @38
    @39
    @26
    @7
    @28
    @25
    @0
    cr
    eleq1
    anbi1d
    @39
    @33
    @37
    vz
    vw
    @39
    @32
    @36
    @15
    @39
    @30
    @19
    @31
    @25
    @0
    @18
    eqeq1
    anbi1d
    anbi1d
    2exbidv
    anbi12d
    @27
    @1
    wceq
    #
    @35
    @9
    @38
    @24
    @40
    @28
    @8
    @7
    @27
    @1
    cr
    eleq1
    anbi2d
    @40
    @37
    @23
    vz
    vw
    @40
    @36
    @22
    @15
    @40
    @31
    @21
    @19
    @27
    @1
    @20
    eqeq1
    anbi2d
    anbi1d
    2exbidv
    anbi12d
    vx
    vy
    vz
    vw
    df-lt
    brab
    baib
    @23
    @16
    vz
    vw
    @22
    @14
    @15
    @22
    cA
    @12
    wceq
    #
    cB
    @13
    wceq
    #
    wa
    @14
    @19
    @41
    @21
    @42
    @18
    @0
    wceq
    @12
    cA
    wceq
    @19
    @41
    @12
    cA
    vz
    vex
    #
    eqresr
    @0
    @18
    eqcom
    cA
    @12
    eqcom
    3bitr4i
    @20
    @1
    wceq
    @13
    cB
    wceq
    @21
    @42
    @13
    cB
    vw
    vex
    #
    eqresr
    @1
    @20
    eqcom
    cB
    @13
    eqcom
    3bitr4i
    anbi12i
    cA
    cB
    @12
    @13
    @43
    @44
    opth2
    bitr4i
    anbi1i
    2exbii
    syl6bb
    syl2anbr
    @15
    @6
    vz
    vw
    cA
    cB
    cnr
    cnr
    @12
    cA
    @13
    cB
    cltr
    breq12
    copsex2g
    bitrd
    pm5.21nii
end
