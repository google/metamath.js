include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "weq.mm"
include "wrmo.mm"
include "wor.mm"
include "wcel.mm"
include "ancom.mm"
include "anbi2ci.mm"
include "an42.mm"
include "3bitr4i.mm"
include "ralnex.mm"
include "breq2.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "breq1.mm"
include "cbvrexv.mm"
include "syl6ibr.mm"
include "con3d.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "anim12d.mm"
include "imp.mm"
include "ancomd.mm"
include "ex.mm"
include "sotrieq2.mm"
include "sylibrd.mm"
include "ralrimivva.mm"
include "syl.mm"
include "notbid.mm"
include "ralbidv.mm"
include "imbi1d.mm"
include "anbi12d.mm"
include "rmo4.mm"
include "sylibr.mm"

theorem infmo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  let vw: setvar w
  assume infmo.1: |- ( ph -> R Or A )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint R w
  disjoint B w
  disjoint ph w
  assert |- ( ph -> E* x e. A ( A. y e. B -. y R x /\ A. y e. A ( x R y -> E. z e. B z R y ) ) )

  proof
    wph
    vy
    cv
    #
    vx
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cB
    wral
    #
    @1
    @0
    cR
    wbr
    #
    vz
    cv
    #
    @0
    cR
    wbr
    #
    vz
    cB
    wrex
    #
    wi
    #
    vy
    cA
    wral
    #
    wa
    #
    @0
    vw
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cB
    wral
    #
    @12
    @0
    cR
    wbr
    #
    @8
    wi
    #
    vy
    cA
    wral
    #
    wa
    #
    wa
    #
    vx
    vw
    weq
    #
    wi
    #
    vw
    cA
    wral
    vx
    cA
    wral
    #
    @11
    vx
    cA
    wrmo
    wph
    cA
    cR
    wor
    #
    @23
    infmo.1
    @24
    @22
    vx
    vw
    cA
    cA
    @24
    @1
    cA
    wcel
    #
    @12
    cA
    wcel
    #
    wa
    wa
    #
    @20
    @1
    @12
    cR
    wbr
    #
    wn
    #
    @12
    @1
    cR
    wbr
    #
    wn
    #
    wa
    #
    @21
    @20
    @18
    @4
    wa
    #
    @10
    @15
    wa
    #
    wa
    #
    @27
    @32
    @4
    @15
    wa
    #
    @18
    @10
    wa
    #
    wa
    @37
    @15
    @4
    wa
    #
    wa
    @20
    @35
    @36
    @38
    @37
    @4
    @15
    ancom
    anbi2ci
    @4
    @10
    @15
    @18
    an42
    @18
    @4
    @10
    @15
    an42
    3bitr4i
    @27
    @35
    @32
    @27
    @35
    wa
    @31
    @29
    @27
    @35
    @31
    @29
    wa
    @27
    @33
    @31
    @34
    @29
    @25
    @33
    @31
    wi
    @24
    @26
    @25
    @18
    @4
    @31
    @4
    @2
    vy
    cB
    wrex
    #
    wn
    @25
    @18
    wa
    #
    @31
    @2
    vy
    cB
    ralnex
    @40
    @30
    @39
    @40
    @30
    @6
    @1
    cR
    wbr
    #
    vz
    cB
    wrex
    #
    @39
    @17
    @30
    @42
    wi
    vy
    @1
    cA
    vy
    vx
    weq
    #
    @16
    @30
    @8
    @42
    @0
    @1
    @12
    cR
    breq2
    @43
    @7
    @41
    vz
    cB
    @0
    @1
    @6
    cR
    breq2
    rexbidv
    imbi12d
    rspcva
    @2
    @41
    vy
    vz
    cB
    @0
    @6
    @1
    cR
    breq1
    cbvrexv
    syl6ibr
    con3d
    syl5bi
    expimpd
    ad2antrl
    @26
    @34
    @29
    wi
    @24
    @25
    @26
    @10
    @15
    @29
    @15
    @13
    vy
    cB
    wrex
    #
    wn
    @26
    @10
    wa
    #
    @29
    @13
    vy
    cB
    ralnex
    @45
    @28
    @44
    @45
    @28
    @6
    @12
    cR
    wbr
    #
    vz
    cB
    wrex
    #
    @44
    @9
    @28
    @47
    wi
    vy
    @12
    cA
    vy
    vw
    weq
    #
    @5
    @28
    @8
    @47
    @0
    @12
    @1
    cR
    breq2
    @48
    @7
    @46
    vz
    cB
    @0
    @12
    @6
    cR
    breq2
    rexbidv
    imbi12d
    rspcva
    @13
    @46
    vy
    vz
    cB
    @0
    @6
    @12
    cR
    breq1
    cbvrexv
    syl6ibr
    con3d
    syl5bi
    expimpd
    ad2antll
    anim12d
    imp
    ancomd
    ex
    syl5bi
    cA
    @1
    @12
    cR
    sotrieq2
    sylibrd
    ralrimivva
    syl
    @11
    @19
    vx
    vw
    cA
    @21
    @4
    @15
    @10
    @18
    @21
    @3
    @14
    vy
    cB
    @21
    @2
    @13
    @1
    @12
    @0
    cR
    breq2
    notbid
    ralbidv
    @21
    @9
    @17
    vy
    cA
    @21
    @5
    @16
    @8
    @1
    @12
    @0
    cR
    breq1
    imbi1d
    ralbidv
    anbi12d
    rmo4
    sylibr
end
