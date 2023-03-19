include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "oveq2.mm"
include "rspc2va.mm"

theorem ovrspc2v
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cX: class X
  let cY: class Y
  let wph: wff ph
  let cG: class G

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint F x
  disjoint F y
  disjoint Y y
  disjoint X x
  disjoint X y
  disjoint ph x
  disjoint ph y
  disjoint G x
  disjoint G y
  assert |- ( ( ( X e. A /\ Y e. B ) /\ A. x e. A A. y e. B ( x F y ) e. C ) -> ( X F Y ) e. C )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    cC
    wcel
    cX
    cY
    cF
    co
    #
    cC
    wcel
    cX
    @1
    cF
    co
    #
    cC
    wcel
    vx
    vy
    cX
    cY
    cA
    cB
    @0
    cX
    wceq
    @2
    @4
    cC
    @0
    cX
    @1
    cF
    oveq1
    eleq1d
    @1
    cY
    wceq
    @4
    @3
    cC
    @1
    cY
    cX
    cF
    oveq2
    eleq1d
    rspc2va
end
