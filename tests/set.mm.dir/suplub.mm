include "cv.mm"
include "csup.mm"
include "wbr.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "crab.mm"
include "wn.mm"
include "simpr.mm"
include "wceq.mm"
include "breq1.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "a1i.mm"
include "ss2rabi.mm"
include "crio.mm"
include "supval2.mm"
include "wreu.mm"
include "supeu.mm"
include "riotacl2.mm"
include "syl.mm"
include "eqeltrd.mm"
include "sseldi.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "simprbi.mm"
include "rspccv.mm"
include "impd.mm"

theorem suplub
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vw: setvar w
  assume supmo.1: |- ( ph -> R Or A )
  assume supcl.2: |- ( ph -> E. x e. A ( A. y e. B -. x R y /\ A. y e. A ( y R x -> E. z e. B y R z ) ) )

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
  disjoint C z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint R w
  disjoint B w
  disjoint C w
  disjoint ph w
  assert |- ( ph -> ( ( C e. A /\ C R sup ( B , A , R ) ) -> E. z e. B C R z ) )

  proof
    wph
    vw
    cv
    #
    cB
    cA
    cR
    csup
    #
    cR
    wbr
    #
    @0
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
    vw
    cA
    wral
    #
    cC
    cA
    wcel
    #
    cC
    @1
    cR
    wbr
    #
    wa
    cC
    @3
    cR
    wbr
    #
    vz
    cB
    wrex
    #
    wi
    wph
    @1
    @0
    vx
    cv
    #
    cR
    wbr
    #
    @5
    wi
    #
    vw
    cA
    wral
    #
    vx
    cA
    crab
    #
    wcel
    #
    @7
    wph
    @12
    vy
    cv
    #
    cR
    wbr
    wn
    vy
    cB
    wral
    #
    @18
    @12
    cR
    wbr
    #
    @18
    @3
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
    vx
    cA
    crab
    #
    @16
    @1
    @25
    @15
    vx
    cA
    @25
    @15
    wi
    @12
    cA
    wcel
    @25
    @24
    @15
    @19
    @24
    simpr
    @23
    @14
    vy
    vw
    cA
    @18
    @0
    wceq
    #
    @20
    @13
    @22
    @5
    @18
    @0
    @12
    cR
    breq1
    @27
    @21
    @4
    vz
    cB
    @18
    @0
    @3
    cR
    breq1
    rexbidv
    imbi12d
    cbvralv
    sylib
    a1i
    ss2rabi
    wph
    @1
    @25
    vx
    cA
    crio
    #
    @26
    wph
    vx
    vy
    vz
    cA
    cB
    cR
    supmo.1
    supval2
    wph
    @25
    vx
    cA
    wreu
    @28
    @26
    wcel
    wph
    vx
    vy
    vz
    cA
    cB
    cR
    supmo.1
    supcl.2
    supeu
    @25
    vx
    cA
    riotacl2
    syl
    eqeltrd
    sseldi
    @17
    @1
    cA
    wcel
    @7
    @15
    @7
    vx
    @1
    cA
    @12
    @1
    wceq
    #
    @14
    @6
    vw
    cA
    @29
    @13
    @2
    @5
    @12
    @1
    @0
    cR
    breq2
    imbi1d
    ralbidv
    elrab
    simprbi
    syl
    @7
    @8
    @9
    @11
    @6
    @9
    @11
    wi
    vw
    cC
    cA
    @0
    cC
    wceq
    #
    @2
    @9
    @5
    @11
    @0
    cC
    @1
    cR
    breq1
    @30
    @4
    @10
    vz
    cB
    @0
    cC
    @3
    cR
    breq1
    rexbidv
    imbi12d
    rspccv
    impd
    syl
end
