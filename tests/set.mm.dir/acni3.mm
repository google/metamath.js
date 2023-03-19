include "wacn.mm"
include "wcel.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "crab.mm"
include "wex.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "rabn0.mm"
include "biimpri.mm"
include "ssrab2.mm"
include "jctil.mm"
include "ralimi.mm"
include "acni2.mm"
include "sylan2.mm"
include "elrab.mm"
include "simprbi.mm"
include "anim2i.mm"
include "eximi.mm"
include "syl.mm"

theorem acni3
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vg: setvar g
  let cX: class X
  let vf: setvar f
  let vh: setvar h
  let vz: setvar z
  let cB: class B
  let cF: class F
  let cC: class C
  assume acni3.1: |- ( y = ( g ` x ) -> ( ph <-> ps ) )

  disjoint g x
  disjoint g y
  disjoint A g
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint g ph
  disjoint ps y
  disjoint X g
  disjoint X x
  disjoint X y
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g h
  disjoint g z
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B g
  disjoint B y
  disjoint B z
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint C f
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint X f
  disjoint X h
  assert |- ( ( X e. AC_ A /\ A. x e. A E. y e. X ph ) -> E. g ( g : A --> X /\ A. x e. A ps ) )

  proof
    cX
    cA
    wacn
    wcel
    #
    wph
    vy
    cX
    wrex
    #
    vx
    cA
    wral
    #
    wa
    cA
    cX
    vg
    cv
    #
    wf
    #
    vx
    cv
    @3
    cfv
    #
    wph
    vy
    cX
    crab
    #
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    vg
    wex
    #
    @4
    wps
    vx
    cA
    wral
    #
    wa
    #
    vg
    wex
    @2
    @0
    @6
    cX
    wss
    #
    @6
    c0
    wne
    #
    wa
    #
    vx
    cA
    wral
    @10
    @1
    @15
    vx
    cA
    @1
    @14
    @13
    @14
    @1
    wph
    vy
    cX
    rabn0
    biimpri
    wph
    vy
    cX
    ssrab2
    jctil
    ralimi
    vx
    cA
    @6
    vg
    cX
    acni2
    sylan2
    @9
    @12
    vg
    @8
    @11
    @4
    @7
    wps
    vx
    cA
    @7
    @5
    cX
    wcel
    wps
    wph
    wps
    vy
    @5
    cX
    acni3.1
    elrab
    simprbi
    ralimi
    anim2i
    eximi
    syl
end
