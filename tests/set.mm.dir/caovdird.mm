include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "id.mm"
include "caovdirg.mm"
include "syl13anc.mm"

theorem caovdird
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
  let cH: class H
  let cK: class K
  let cD: class D
  let cR: class R
  let cT: class T
  assume caovdirg.1: |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. K ) ) -> ( ( x F y ) G z ) = ( ( x G z ) H ( y G z ) ) )
  assume caovdird.2: |- ( ph -> A e. S )
  assume caovdird.3: |- ( ph -> B e. S )
  assume caovdird.4: |- ( ph -> C e. K )

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
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ph -> ( ( A F B ) G C ) = ( ( A G C ) H ( B G C ) ) )

  proof
    wph
    wph
    cA
    cS
    wcel
    cB
    cS
    wcel
    cC
    cK
    wcel
    cA
    cB
    cF
    co
    cC
    cG
    co
    cA
    cC
    cG
    co
    cB
    cC
    cG
    co
    cH
    co
    wceq
    wph
    id
    caovdird.2
    caovdird.3
    caovdird.4
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    cS
    cF
    cG
    cH
    cK
    caovdirg.1
    caovdirg
    syl13anc
end
