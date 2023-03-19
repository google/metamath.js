include "co.mm"
include "wceq.mm"
include "caovcomd.mm"
include "eqeq12d.mm"
include "caovcand.mm"
include "bitr3d.mm"

theorem caovcanrd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let cF: class F
  let cD: class D
  let cG: class G
  let cH: class H
  let cK: class K
  let cR: class R
  assume caovcang.1: |- ( ( ph /\ ( x e. T /\ y e. S /\ z e. S ) ) -> ( ( x F y ) = ( x F z ) <-> y = z ) )
  assume caovcand.2: |- ( ph -> A e. T )
  assume caovcand.3: |- ( ph -> B e. S )
  assume caovcand.4: |- ( ph -> C e. S )
  assume caovcanrd.5: |- ( ph -> A e. S )
  assume caovcanrd.6: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) )

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
  disjoint T x
  disjoint T y
  disjoint T z
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
  assert |- ( ph -> ( ( B F A ) = ( C F A ) <-> B = C ) )

  proof
    wph
    cA
    cB
    cF
    co
    #
    cA
    cC
    cF
    co
    #
    wceq
    cB
    cA
    cF
    co
    #
    cC
    cA
    cF
    co
    #
    wceq
    cB
    cC
    wceq
    wph
    @0
    @2
    @1
    @3
    wph
    vx
    vy
    cA
    cB
    cS
    cF
    caovcanrd.6
    caovcanrd.5
    caovcand.3
    caovcomd
    wph
    vx
    vy
    cA
    cC
    cS
    cF
    caovcanrd.6
    caovcanrd.5
    caovcand.4
    caovcomd
    eqeq12d
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    cS
    cT
    cF
    caovcang.1
    caovcand.2
    caovcand.3
    caovcand.4
    caovcand
    bitr3d
end
