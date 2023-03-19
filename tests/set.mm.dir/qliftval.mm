include "cv.mm"
include "cec.mm"
include "cqs.mm"
include "qliftlem.mm"
include "eceq1.mm"
include "fliftval.mm"

theorem qliftval
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  assume qlift.1: |- F = ran ( x e. X |-> <. [ x ] R , A >. )
  assume qlift.2: |- ( ( ph /\ x e. X ) -> A e. Y )
  assume qlift.3: |- ( ph -> R Er X )
  assume qlift.4: |- ( ph -> X e. _V )
  assume qliftval.4: |- ( x = C -> A = B )
  assume qliftval.6: |- ( ph -> Fun F )

  disjoint B x
  disjoint C x
  disjoint ph x
  disjoint R x
  disjoint X x
  disjoint Y x
  disjoint y z
  disjoint A y
  disjoint A z
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
  assert |- ( ( ph /\ C e. X ) -> ( F ` [ C ] R ) = B )

  proof
    wph
    vx
    vx
    cv
    #
    cR
    cec
    cA
    cC
    cR
    cec
    cB
    cX
    cR
    cqs
    cY
    cF
    cX
    cC
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
    @0
    cC
    cR
    eceq1
    qliftval.4
    qliftval.6
    fliftval
end
