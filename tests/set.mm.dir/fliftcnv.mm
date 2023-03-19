include "ccnv.mm"
include "wrel.mm"
include "cop.mm"
include "cmpt.mm"
include "crn.mm"
include "wa.mm"
include "wceq.mm"
include "cxp.mm"
include "wss.mm"
include "eqid.mm"
include "fliftrel.mm"
include "relxp.mm"
include "relss.mm"
include "mpisyl.mm"
include "relcnv.mm"
include "jctil.mm"
include "cv.mm"
include "wbr.mm"
include "wcel.mm"
include "wrex.mm"
include "fliftel.mm"
include "vex.mm"
include "brcnv.mm"
include "ancom.mm"
include "rexbii.mm"
include "3bitr4g.mm"
include "bitr4d.mm"
include "df-br.mm"
include "3bitr3g.mm"
include "eqrelrdv2.mm"
include "mpancom.mm"

theorem fliftcnv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cY: class Y
  let cD: class D
  assume flift.1: |- F = ran ( x e. X |-> <. A , B >. )
  assume flift.2: |- ( ( ph /\ x e. X ) -> A e. R )
  assume flift.3: |- ( ( ph /\ x e. X ) -> B e. S )

  disjoint R x
  disjoint ph x
  disjoint X x
  disjoint S x
  disjoint u v
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B u
  disjoint B v
  disjoint B y
  disjoint B z
  disjoint u x
  disjoint C u
  disjoint v x
  disjoint C v
  disjoint x z
  disjoint C x
  disjoint C z
  disjoint x y
  disjoint R y
  disjoint R z
  disjoint Y x
  disjoint D u
  disjoint D v
  disjoint D x
  disjoint D z
  disjoint F u
  disjoint F v
  disjoint F y
  disjoint F z
  disjoint ph u
  disjoint ph v
  disjoint ph y
  disjoint ph z
  disjoint X u
  disjoint X v
  disjoint X y
  disjoint X z
  disjoint S y
  disjoint S z
  assert |- ( ph -> `' F = ran ( x e. X |-> <. B , A >. ) )

  proof
    cF
    ccnv
    #
    wrel
    #
    vx
    cX
    cB
    cA
    cop
    cmpt
    crn
    #
    wrel
    #
    wa
    wph
    @0
    @2
    wceq
    wph
    @3
    @1
    wph
    @2
    cS
    cR
    cxp
    #
    wss
    @4
    wrel
    @3
    wph
    vx
    cB
    cA
    cS
    cR
    @2
    cX
    @2
    eqid
    #
    flift.3
    flift.2
    fliftrel
    cS
    cR
    relxp
    @2
    @4
    relss
    mpisyl
    cF
    relcnv
    jctil
    wph
    vy
    vz
    @0
    @2
    wph
    vy
    cv
    #
    vz
    cv
    #
    @0
    wbr
    #
    @6
    @7
    @2
    wbr
    #
    @6
    @7
    cop
    #
    @0
    wcel
    @10
    @2
    wcel
    wph
    @8
    @6
    cB
    wceq
    #
    @7
    cA
    wceq
    #
    wa
    #
    vx
    cX
    wrex
    #
    @9
    wph
    @7
    @6
    cF
    wbr
    @12
    @11
    wa
    #
    vx
    cX
    wrex
    @8
    @14
    wph
    vx
    cA
    cB
    @7
    @6
    cR
    cS
    cF
    cX
    flift.1
    flift.2
    flift.3
    fliftel
    @6
    @7
    cF
    vy
    vex
    vz
    vex
    brcnv
    @13
    @15
    vx
    cX
    @11
    @12
    ancom
    rexbii
    3bitr4g
    wph
    vx
    cB
    cA
    @6
    @7
    cS
    cR
    @2
    cX
    @5
    flift.3
    flift.2
    fliftel
    bitr4d
    @6
    @7
    @0
    df-br
    @6
    @7
    @2
    df-br
    3bitr3g
    eqrelrdv2
    mpancom
end
