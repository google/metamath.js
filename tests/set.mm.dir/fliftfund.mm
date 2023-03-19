include "wfun.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "3exp2.mm"
include "imp32.mm"
include "ralrimivva.mm"
include "fliftfun.mm"
include "mpbird.mm"

theorem fliftfund
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let cY: class Y
  assume flift.1: |- F = ran ( x e. X |-> <. A , B >. )
  assume flift.2: |- ( ( ph /\ x e. X ) -> A e. R )
  assume flift.3: |- ( ( ph /\ x e. X ) -> B e. S )
  assume fliftfun.4: |- ( x = y -> A = C )
  assume fliftfun.5: |- ( x = y -> B = D )
  assume fliftfund.6: |- ( ( ph /\ ( x e. X /\ y e. X /\ A = C ) ) -> B = D )

  disjoint A y
  disjoint B y
  disjoint C x
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint D x
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint S x
  disjoint S y
  disjoint u v
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint y z
  disjoint A z
  disjoint B u
  disjoint B v
  disjoint B z
  disjoint u x
  disjoint C u
  disjoint v x
  disjoint C v
  disjoint x z
  disjoint C z
  disjoint R z
  disjoint Y x
  disjoint D u
  disjoint D v
  disjoint D z
  disjoint F u
  disjoint F v
  disjoint F z
  disjoint ph u
  disjoint ph v
  disjoint ph z
  disjoint X u
  disjoint X v
  disjoint X z
  disjoint S z
  assert |- ( ph -> Fun F )

  proof
    wph
    cF
    wfun
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wi
    #
    vy
    cX
    wral
    vx
    cX
    wral
    wph
    @2
    vx
    vy
    cX
    cX
    wph
    vx
    cv
    cX
    wcel
    #
    vy
    cv
    cX
    wcel
    #
    @2
    wph
    @3
    @4
    @0
    @1
    fliftfund.6
    3exp2
    imp32
    ralrimivva
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    cR
    cS
    cF
    cX
    flift.1
    flift.2
    flift.3
    fliftfun.4
    fliftfun.5
    fliftfun
    mpbird
end
