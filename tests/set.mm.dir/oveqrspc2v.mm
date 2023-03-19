include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "ralrimivva.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "mpan9.mm"

theorem oveqrspc2v
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let cC: class C
  assume oveqrspc2v.1: |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( x F y ) = ( x G y ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint Y y
  disjoint G x
  disjoint G y
  disjoint X x
  disjoint X y
  disjoint C x
  disjoint C y
  assert |- ( ( ph /\ ( X e. A /\ Y e. B ) ) -> ( X F Y ) = ( X G Y ) )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    @0
    @1
    cG
    co
    #
    wceq
    #
    vy
    cB
    wral
    vx
    cA
    wral
    cX
    cA
    wcel
    cY
    cB
    wcel
    wa
    cX
    cY
    cF
    co
    #
    cX
    cY
    cG
    co
    #
    wceq
    #
    wph
    @4
    vx
    vy
    cA
    cB
    oveqrspc2v.1
    ralrimivva
    @4
    @7
    cX
    @1
    cF
    co
    #
    cX
    @1
    cG
    co
    #
    wceq
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
    @8
    @3
    @9
    @0
    cX
    @1
    cF
    oveq1
    @0
    cX
    @1
    cG
    oveq1
    eqeq12d
    @1
    cY
    wceq
    @8
    @5
    @9
    @6
    @1
    cY
    cX
    cF
    oveq2
    @1
    cY
    cX
    cG
    oveq2
    eqeq12d
    rspc2v
    mpan9
end
