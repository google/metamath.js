include "wrex.mm"
include "weq.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "cv.mm"
include "wcel.mm"
include "wreu.mm"
include "wrmo.mm"
include "r19.29r.mm"
include "reximi.mm"
include "pm3.35.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "biimpac.mm"
include "ancomd.mm"
include "ex.mm"
include "rexlimivv.mm"
include "4syl.mm"
include "pm4.71rd.mm"
include "anass.mm"
include "syl6bb.mm"
include "2exbidv.mm"
include "pm5.32i.mm"
include "2reu5lem3.mm"
include "df-rex.mm"
include "r19.42v.mm"
include "bitr3i.mm"
include "exbii.mm"
include "bitri.mm"
include "anbi2i.mm"
include "3bitr4i.mm"

theorem 2reu5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B

  disjoint w y
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint B w
  disjoint x z
  disjoint B x
  disjoint B z
  disjoint x y
  disjoint ph w
  disjoint ph z
  disjoint A x
  disjoint B y
  assert |- ( ( E! x e. A E! y e. B ph /\ A. x e. A E* y e. B ph ) <-> ( E. x e. A E. y e. B ph /\ E. z e. A E. w e. B A. x e. A A. y e. B ( ph -> ( x = z /\ y = w ) ) ) )

  proof
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    #
    wph
    vx
    vz
    weq
    #
    vy
    vw
    weq
    #
    wa
    #
    wi
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    vw
    wex
    vz
    wex
    #
    wa
    @1
    vw
    cv
    #
    cB
    wcel
    #
    vz
    cv
    #
    cA
    wcel
    #
    @7
    wa
    #
    wa
    #
    vw
    wex
    #
    vz
    wex
    #
    wa
    wph
    vy
    cB
    wreu
    vx
    cA
    wreu
    wph
    vy
    cB
    wrmo
    vx
    cA
    wral
    wa
    @1
    @7
    vw
    cB
    wrex
    #
    vz
    cA
    wrex
    #
    wa
    @1
    @8
    @16
    @1
    @7
    @14
    vz
    vw
    @1
    @7
    @10
    @12
    wa
    #
    @7
    wa
    @14
    @1
    @7
    @19
    @1
    @7
    @19
    @1
    @7
    wa
    @0
    @6
    wa
    #
    vx
    cA
    wrex
    wph
    @5
    wa
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    @4
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    @19
    @0
    @6
    vx
    cA
    r19.29r
    @20
    @22
    vx
    cA
    wph
    @5
    vy
    cB
    r19.29r
    reximi
    @22
    @23
    vx
    cA
    @21
    @4
    vy
    cB
    wph
    @4
    pm3.35
    reximi
    reximi
    @4
    @19
    vx
    vy
    cA
    cB
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    @4
    @19
    @28
    @4
    wa
    @12
    @10
    @4
    @28
    @12
    @10
    wa
    @2
    @25
    @12
    @3
    @27
    @10
    @24
    @11
    cA
    eleq1
    @26
    @9
    cB
    eleq1
    bi2anan9
    biimpac
    ancomd
    ex
    rexlimivv
    4syl
    ex
    pm4.71rd
    @10
    @12
    @7
    anass
    syl6bb
    2exbidv
    pm5.32i
    wph
    vx
    vy
    vz
    vw
    cA
    cB
    2reu5lem3
    @18
    @16
    @1
    @18
    @12
    @17
    wa
    #
    vz
    wex
    @16
    @17
    vz
    cA
    df-rex
    @29
    @15
    vz
    @29
    @13
    vw
    cB
    wrex
    @15
    @12
    @7
    vw
    cB
    r19.42v
    @13
    vw
    cB
    df-rex
    bitr3i
    exbii
    bitri
    anbi2i
    3bitr4i
end
