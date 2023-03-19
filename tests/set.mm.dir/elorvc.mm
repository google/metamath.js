include "cv.mm"
include "corvc.mm"
include "co.mm"
include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "wbr.mm"
include "crab.mm"
include "wa.mm"
include "orvcval2.mm"
include "eleq2d.mm"
include "rabid.mm"
include "syl6bb.mm"
include "baibd.mm"

theorem elorvc
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cR: class R
  let cV: class V
  let cW: class W
  let cX: class X
  let va: setvar a
  let vx: setvar x
  let vy: setvar y
  assume orvcval.1: |- ( ph -> Fun X )
  assume orvcval.2: |- ( ph -> X e. V )
  assume orvcval.3: |- ( ph -> A e. W )

  disjoint A z
  disjoint R z
  disjoint X z
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint R a
  disjoint R x
  disjoint R y
  disjoint X a
  disjoint X x
  disjoint X y
  disjoint a ph
  disjoint ph x
  disjoint y z
  assert |- ( ( ph /\ z e. dom X ) -> ( z e. ( X oRVC R A ) <-> ( X ` z ) R A ) )

  proof
    wph
    vz
    cv
    #
    cX
    cA
    cR
    corvc
    co
    #
    wcel
    #
    @0
    cX
    cdm
    #
    wcel
    #
    @0
    cX
    cfv
    cA
    cR
    wbr
    #
    wph
    @2
    @0
    @5
    vz
    @3
    crab
    #
    wcel
    @4
    @5
    wa
    wph
    @1
    @6
    @0
    wph
    vz
    cA
    cR
    cV
    cW
    cX
    orvcval.1
    orvcval.2
    orvcval.3
    orvcval2
    eleq2d
    @5
    vz
    @3
    rabid
    syl6bb
    baibd
end
