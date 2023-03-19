include "wrex.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wss.mm"
include "df-rex.mm"
include "ralbii.mm"
include "wi.mm"
include "wceq.mm"
include "raleq.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "bnd.mm"
include "vtocl.mm"
include "sylbi.mm"
include "cin.mm"
include "vex.mm"
include "inex1.mm"
include "inss2.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "biantrurd.mm"
include "rexeq.mm"
include "elin.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "rexbii2.mm"
include "syl6bb.mm"
include "ralbidv.mm"
include "bitr3d.mm"
include "spcev.mm"
include "exlimiv.mm"
include "syl.mm"

theorem bnd2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vv: setvar v
  assume bnd2.1: |- A e. _V

  disjoint ph z
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint x y
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint ph w
  disjoint ph v
  disjoint w z
  disjoint v z
  disjoint v w
  disjoint w x
  disjoint v x
  disjoint A w
  disjoint A v
  disjoint w y
  disjoint v y
  disjoint B w
  disjoint B v
  assert |- ( A. x e. A E. y e. B ph -> E. z ( z C_ B /\ A. x e. A E. y e. z ph ) )

  proof
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    vy
    cv
    #
    cB
    wcel
    #
    wph
    wa
    #
    vy
    vw
    cv
    #
    wrex
    #
    vx
    cA
    wral
    #
    vw
    wex
    #
    vz
    cv
    #
    cB
    wss
    #
    wph
    vy
    @9
    wrex
    #
    vx
    cA
    wral
    #
    wa
    #
    vz
    wex
    #
    @1
    @4
    vy
    wex
    #
    vx
    cA
    wral
    #
    @8
    @0
    @15
    vx
    cA
    wph
    vy
    cB
    df-rex
    ralbii
    @15
    vx
    vv
    cv
    #
    wral
    #
    @6
    vx
    @17
    wral
    #
    vw
    wex
    #
    wi
    @16
    @8
    wi
    vv
    cA
    bnd2.1
    @17
    cA
    wceq
    #
    @18
    @16
    @20
    @8
    @15
    vx
    @17
    cA
    raleq
    @21
    @19
    @7
    vw
    @6
    vx
    @17
    cA
    raleq
    exbidv
    imbi12d
    @4
    vx
    vy
    vv
    vw
    bnd
    vtocl
    sylbi
    @7
    @14
    vw
    @13
    @7
    vz
    @5
    cB
    cin
    #
    @5
    cB
    vw
    vex
    inex1
    @9
    @22
    wceq
    #
    @12
    @13
    @7
    @23
    @10
    @12
    @23
    @10
    @22
    cB
    wss
    @5
    cB
    inss2
    @9
    @22
    cB
    sseq1
    mpbiri
    biantrurd
    @23
    @11
    @6
    vx
    cA
    @23
    @11
    wph
    vy
    @22
    wrex
    @6
    wph
    vy
    @9
    @22
    rexeq
    wph
    @4
    vy
    @22
    @5
    @2
    @22
    wcel
    #
    wph
    wa
    @2
    @5
    wcel
    #
    @3
    wa
    #
    wph
    wa
    @25
    @4
    wa
    @24
    @26
    wph
    @2
    @5
    cB
    elin
    anbi1i
    @25
    @3
    wph
    anass
    bitri
    rexbii2
    syl6bb
    ralbidv
    bitr3d
    spcev
    exlimiv
    syl
end
