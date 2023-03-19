include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "cec.mm"
include "cqs.mm"
include "wer.mm"
include "erex.mm"
include "sylc.mm"
include "ecelqsg.mm"
include "sylan.mm"

theorem qliftlem
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
  assert |- ( ( ph /\ x e. X ) -> [ x ] R e. ( X /. R ) )

  proof
    wph
    cR
    cvv
    wcel
    #
    vx
    cv
    #
    cX
    wcel
    @1
    cR
    cec
    cX
    cR
    cqs
    wcel
    wph
    cX
    cR
    wer
    cX
    cvv
    wcel
    @0
    qlift.3
    qlift.4
    cX
    cR
    cvv
    erex
    sylc
    cX
    @1
    cR
    cvv
    ecelqsg
    sylan
end
