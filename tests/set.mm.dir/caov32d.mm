include "co.mm"
include "caovcomd.mm"
include "oveq2d.mm"
include "caovassd.mm"
include "3eqtr4d.mm"

theorem caov32d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cF: class F
  let cD: class D
  let cG: class G
  let cH: class H
  let cK: class K
  let cR: class R
  let cT: class T
  assume caovd.1: |- ( ph -> A e. S )
  assume caovd.2: |- ( ph -> B e. S )
  assume caovd.3: |- ( ph -> C e. S )
  assume caovd.com: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) )
  assume caovd.ass: |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint D x
  disjoint D y
  disjoint D z
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
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ph -> ( ( A F B ) F C ) = ( ( A F C ) F B ) )

  proof
    wph
    cA
    cB
    cC
    cF
    co
    #
    cF
    co
    cA
    cC
    cB
    cF
    co
    #
    cF
    co
    cA
    cB
    cF
    co
    cC
    cF
    co
    cA
    cC
    cF
    co
    cB
    cF
    co
    wph
    @0
    @1
    cA
    cF
    wph
    vx
    vy
    cB
    cC
    cS
    cF
    caovd.com
    caovd.2
    caovd.3
    caovcomd
    oveq2d
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    cS
    cF
    caovd.ass
    caovd.1
    caovd.2
    caovd.3
    caovassd
    wph
    vx
    vy
    vz
    cA
    cC
    cB
    cS
    cF
    caovd.ass
    caovd.1
    caovd.3
    caovd.2
    caovassd
    3eqtr4d
end
