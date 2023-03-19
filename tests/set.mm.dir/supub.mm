include "csup.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wcel.mm"
include "wi.mm"
include "crab.mm"
include "wrex.mm"
include "wa.mm"
include "simpl.mm"
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
include "wceq.mm"
include "breq2.mm"
include "notbid.mm"
include "cbvralv.mm"
include "breq1.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "elrab.mm"
include "simprbi.mm"
include "rspccv.mm"

theorem supub
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
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint R w
  disjoint B w
  disjoint C w
  disjoint ph w
  assert |- ( ph -> ( C e. B -> -. sup ( B , A , R ) R C ) )

  proof
    wph
    cB
    cA
    cR
    csup
    #
    vw
    cv
    #
    cR
    wbr
    #
    wn
    #
    vw
    cB
    wral
    #
    cC
    cB
    wcel
    @0
    cC
    cR
    wbr
    #
    wn
    #
    wi
    wph
    @0
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
    vx
    cA
    crab
    #
    wcel
    #
    @4
    wph
    @11
    @8
    @7
    cR
    wbr
    @8
    vz
    cv
    cR
    wbr
    vz
    cB
    wrex
    wi
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
    @12
    @0
    @15
    @11
    vx
    cA
    @15
    @11
    wi
    @7
    cA
    wcel
    @11
    @14
    simpl
    a1i
    ss2rabi
    wph
    @0
    @15
    vx
    cA
    crio
    #
    @16
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
    @15
    vx
    cA
    wreu
    @17
    @16
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
    @15
    vx
    cA
    riotacl2
    syl
    eqeltrd
    sseldi
    @13
    @0
    cA
    wcel
    @4
    @11
    @4
    vx
    @0
    cA
    @11
    @7
    @1
    cR
    wbr
    #
    wn
    #
    vw
    cB
    wral
    @7
    @0
    wceq
    #
    @4
    @10
    @19
    vy
    vw
    cB
    @8
    @1
    wceq
    @9
    @18
    @8
    @1
    @7
    cR
    breq2
    notbid
    cbvralv
    @20
    @19
    @3
    vw
    cB
    @20
    @18
    @2
    @7
    @0
    @1
    cR
    breq1
    notbid
    ralbidv
    syl5bb
    elrab
    simprbi
    syl
    @3
    @6
    vw
    cC
    cB
    @1
    cC
    wceq
    @2
    @5
    @1
    cC
    @0
    cR
    breq2
    notbid
    rspccv
    syl
end
