include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "ralrimivva.mm"
include "oveq1.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "rspc2v.mm"
include "mpan9.mm"

theorem caovcomg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let vz: setvar z
  let cC: class C
  let cD: class D
  let cG: class G
  let cH: class H
  let cK: class K
  let cR: class R
  let cT: class T
  assume caovcomg.1: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  disjoint F x
  disjoint F y
  disjoint S x
  disjoint S y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint ph z
  disjoint F z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S z
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ( ph /\ ( A e. S /\ B e. S ) ) -> ( A F B ) = ( B F A ) )

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
    @1
    @0
    cF
    co
    #
    wceq
    #
    vy
    cS
    wral
    vx
    cS
    wral
    cA
    cS
    wcel
    cB
    cS
    wcel
    wa
    cA
    cB
    cF
    co
    #
    cB
    cA
    cF
    co
    #
    wceq
    #
    wph
    @4
    vx
    vy
    cS
    cS
    caovcomg.1
    ralrimivva
    @4
    @7
    cA
    @1
    cF
    co
    #
    @1
    cA
    cF
    co
    #
    wceq
    vx
    vy
    cA
    cB
    cS
    cS
    @0
    cA
    wceq
    @2
    @8
    @3
    @9
    @0
    cA
    @1
    cF
    oveq1
    @0
    cA
    @1
    cF
    oveq2
    eqeq12d
    @1
    cB
    wceq
    @8
    @5
    @9
    @6
    @1
    cB
    cA
    cF
    oveq2
    @1
    cB
    cA
    cF
    oveq1
    eqeq12d
    rspc2v
    mpan9
end
