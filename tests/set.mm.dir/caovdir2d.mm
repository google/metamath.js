include "co.mm"
include "caovdid.mm"
include "caovcld.mm"
include "caovcomd.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem caovdir2d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cF: class F
  let cG: class G
  let cD: class D
  let cH: class H
  let cK: class K
  let cR: class R
  let cT: class T
  assume caovdir2d.1: |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( x G ( y F z ) ) = ( ( x G y ) F ( x G z ) ) )
  assume caovdir2d.2: |- ( ph -> A e. S )
  assume caovdir2d.3: |- ( ph -> B e. S )
  assume caovdir2d.4: |- ( ph -> C e. S )
  assume caovdir2d.cl: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) e. S )
  assume caovdir2d.com: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x G y ) = ( y G x ) )

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
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint D x
  disjoint D y
  disjoint D z
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
  assert |- ( ph -> ( ( A F B ) G C ) = ( ( A G C ) F ( B G C ) ) )

  proof
    wph
    cC
    cA
    cB
    cF
    co
    #
    cG
    co
    cC
    cA
    cG
    co
    #
    cC
    cB
    cG
    co
    #
    cF
    co
    @0
    cC
    cG
    co
    cA
    cC
    cG
    co
    #
    cB
    cC
    cG
    co
    #
    cF
    co
    wph
    vx
    vy
    vz
    cC
    cA
    cB
    cS
    cF
    cG
    cF
    cS
    caovdir2d.1
    caovdir2d.4
    caovdir2d.2
    caovdir2d.3
    caovdid
    wph
    vx
    vy
    @0
    cC
    cS
    cG
    caovdir2d.com
    wph
    vx
    vy
    cA
    cB
    cS
    cS
    cS
    cF
    caovdir2d.cl
    caovdir2d.2
    caovdir2d.3
    caovcld
    caovdir2d.4
    caovcomd
    wph
    @3
    @1
    @4
    @2
    cF
    wph
    vx
    vy
    cA
    cC
    cS
    cG
    caovdir2d.com
    caovdir2d.2
    caovdir2d.4
    caovcomd
    wph
    vx
    vy
    cB
    cC
    cS
    cG
    caovdir2d.com
    caovdir2d.3
    caovdir2d.4
    caovcomd
    oveq12d
    3eqtr4d
end
