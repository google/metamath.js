include "corvc.mm"
include "co.mm"
include "ccnv.mm"
include "cv.mm"
include "wbr.mm"
include "cab.mm"
include "cima.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "crab.mm"
include "orvcval.mm"
include "wfn.mm"
include "wceq.mm"
include "wfun.mm"
include "funfn.mm"
include "sylib.mm"
include "fncnvima2.mm"
include "syl.mm"
include "fvex.mm"
include "breq1.mm"
include "elab.mm"
include "rabbii.mm"
include "a1i.mm"
include "3eqtrd.mm"

theorem orvcval2
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
  assert |- ( ph -> ( X oRVC R A ) = { z e. dom X | ( X ` z ) R A } )

  proof
    wph
    cX
    cA
    cR
    corvc
    co
    cX
    ccnv
    vy
    cv
    #
    cA
    cR
    wbr
    #
    vy
    cab
    #
    cima
    #
    vz
    cv
    #
    cX
    cfv
    #
    @2
    wcel
    #
    vz
    cX
    cdm
    #
    crab
    #
    @5
    cA
    cR
    wbr
    #
    vz
    @7
    crab
    #
    wph
    vy
    cA
    cR
    cV
    cW
    cX
    orvcval.1
    orvcval.2
    orvcval.3
    orvcval
    wph
    cX
    @7
    wfn
    #
    @3
    @8
    wceq
    wph
    cX
    wfun
    @11
    orvcval.1
    cX
    funfn
    sylib
    vz
    @7
    @2
    cX
    fncnvima2
    syl
    @8
    @10
    wceq
    wph
    @6
    @9
    vz
    @7
    @1
    @9
    vy
    @5
    @4
    cX
    fvex
    @0
    @5
    cA
    cR
    breq1
    elab
    rabbii
    a1i
    3eqtrd
end
