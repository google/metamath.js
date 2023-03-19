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
include "breq1.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "breq2.mm"
include "cbvrexv.mm"
include "syl6ibr.mm"
include "con3d.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "anim12d.mm"
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

theorem supmo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  let vw: setvar w
  let cC: class C
  assume supmo.1: |- ( ph -> R Or A )

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
  disjoint C w
  disjoint ph w
  assert |- ( ph -> E* x e. A ( A. y e. B -. x R y /\ A. y e. A ( y R x -> E. z e. B y R z ) ) )

  proof
    wph
    vx
    cv
    #
    vy
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
    @1
    vz
    cv
    #
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
    vw
    cv
    #
    @1
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
    @12
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
    supmo.1
    @24
    @22
    vx
    vw
    cA
    cA
    @24
    @0
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
    @0
    @12
    cR
    wbr
    #
    wn
    #
    @12
    @0
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
    @33
    @29
    @34
    @31
    @25
    @33
    @29
    wi
    @24
    @26
    @25
    @18
    @4
    @29
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
    @29
    @2
    vy
    cB
    ralnex
    @40
    @28
    @39
    @40
    @28
    @0
    @6
    cR
    wbr
    #
    vz
    cB
    wrex
    #
    @39
    @17
    @28
    @42
    wi
    vy
    @0
    cA
    vy
    vx
    weq
    #
    @16
    @28
    @8
    @42
    @1
    @0
    @12
    cR
    breq1
    @43
    @7
    @41
    vz
    cB
    @1
    @0
    @6
    cR
    breq1
    rexbidv
    imbi12d
    rspcva
    @2
    @41
    vy
    vz
    cB
    @1
    @6
    @0
    cR
    breq2
    cbvrexv
    syl6ibr
    con3d
    syl5bi
    expimpd
    ad2antrl
    @26
    @34
    @31
    wi
    @24
    @25
    @26
    @10
    @15
    @31
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
    @31
    @13
    vy
    cB
    ralnex
    @45
    @30
    @44
    @45
    @30
    @12
    @6
    cR
    wbr
    #
    vz
    cB
    wrex
    #
    @44
    @9
    @30
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
    @30
    @8
    @47
    @1
    @12
    @0
    cR
    breq1
    @48
    @7
    @46
    vz
    cB
    @1
    @12
    @6
    cR
    breq1
    rexbidv
    imbi12d
    rspcva
    @13
    @46
    vy
    vz
    cB
    @1
    @6
    @12
    cR
    breq2
    cbvrexv
    syl6ibr
    con3d
    syl5bi
    expimpd
    ad2antll
    anim12d
    syl5bi
    cA
    @0
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
    @0
    @12
    @1
    cR
    breq1
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
    @0
    @12
    @1
    cR
    breq2
    imbi1d
    ralbidv
    anbi12d
    rmo4
    sylibr
end
