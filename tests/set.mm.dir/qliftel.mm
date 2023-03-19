include "cec.mm"
include "wbr.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cqs.mm"
include "qliftlem.mm"
include "fliftel.mm"
include "wcel.mm"
include "wer.mm"
include "adantr.mm"
include "simpr.mm"
include "erth2.mm"
include "anbi1d.mm"
include "rexbidva.mm"
include "bitr4d.mm"

theorem qliftel
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  assume qlift.1: |- F = ran ( x e. X |-> <. [ x ] R , A >. )
  assume qlift.2: |- ( ( ph /\ x e. X ) -> A e. Y )
  assume qlift.3: |- ( ph -> R Er X )
  assume qlift.4: |- ( ph -> X e. _V )

  disjoint C x
  disjoint D x
  disjoint ph x
  disjoint R x
  disjoint X x
  disjoint Y x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
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
  assert |- ( ph -> ( [ C ] R F D <-> E. x e. X ( C R x /\ D = A ) ) )

  proof
    wph
    cC
    cR
    cec
    #
    cD
    cF
    wbr
    @0
    vx
    cv
    #
    cR
    cec
    #
    wceq
    #
    cD
    cA
    wceq
    #
    wa
    #
    vx
    cX
    wrex
    cC
    @1
    cR
    wbr
    #
    @4
    wa
    #
    vx
    cX
    wrex
    wph
    vx
    @2
    cA
    @0
    cD
    cX
    cR
    cqs
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
    fliftel
    wph
    @7
    @5
    vx
    cX
    wph
    @1
    cX
    wcel
    #
    wa
    #
    @6
    @3
    @4
    @9
    cC
    @1
    cR
    cX
    wph
    cX
    cR
    wer
    @8
    qlift.3
    adantr
    wph
    @8
    simpr
    erth2
    anbi1d
    rexbidva
    bitr4d
end
