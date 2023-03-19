include "wfun.mm"
include "cv.mm"
include "cec.mm"
include "cmpt.mm"
include "crn.mm"
include "wf.mm"
include "cqs.mm"
include "qliftlem.mm"
include "fliftf.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "df-qs.mm"
include "eqid.mm"
include "rnmpt.mm"
include "eqtr4i.mm"
include "a1i.mm"
include "feq2d.mm"
include "bitr4d.mm"

theorem qliftf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cF: class F
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D
  assume qlift.1: |- F = ran ( x e. X |-> <. [ x ] R , A >. )
  assume qlift.2: |- ( ( ph /\ x e. X ) -> A e. Y )
  assume qlift.3: |- ( ph -> R Er X )
  assume qlift.4: |- ( ph -> X e. _V )

  disjoint ph x
  disjoint R x
  disjoint X x
  disjoint Y x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint x y
  disjoint x z
  disjoint ph y
  disjoint ph z
  disjoint R y
  disjoint R z
  disjoint F y
  disjoint F z
  disjoint X y
  disjoint X z
  disjoint Y y
  disjoint Y z
  assert |- ( ph -> ( Fun F <-> F : ( X /. R ) --> Y ) )

  proof
    wph
    cF
    wfun
    vx
    cX
    vx
    cv
    cR
    cec
    #
    cmpt
    #
    crn
    #
    cY
    cF
    wf
    cX
    cR
    cqs
    #
    cY
    cF
    wf
    wph
    vx
    @0
    cA
    @3
    cY
    cF
    cX
    qlift.1
    wph
    vx
    cA
    cR
    cF
    cX
    cY
    qlift.1
    qlift.2
    qlift.3
    qlift.4
    qliftlem
    qlift.2
    fliftf
    wph
    @3
    @2
    cY
    cF
    @3
    @2
    wceq
    wph
    @3
    vy
    cv
    @0
    wceq
    vx
    cX
    wrex
    vy
    cab
    @2
    vx
    vy
    cX
    cR
    df-qs
    vx
    vy
    cX
    @0
    @1
    @1
    eqid
    rnmpt
    eqtr4i
    a1i
    feq2d
    bitr4d
end
