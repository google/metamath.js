include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "id.mm"
include "caovdig.mm"
include "syl13anc.mm"

theorem caovdid
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
  assume caovdig.1: |- ( ( ph /\ ( x e. K /\ y e. S /\ z e. S ) ) -> ( x G ( y F z ) ) = ( ( x G y ) H ( x G z ) ) )
  assume caovdid.2: |- ( ph -> A e. K )
  assume caovdid.3: |- ( ph -> B e. S )
  assume caovdid.4: |- ( ph -> C e. S )

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
  assert |- ( ph -> ( A G ( B F C ) ) = ( ( A G B ) H ( A G C ) ) )

  proof
    wph
    wph
    cA
    cK
    wcel
    cB
    cS
    wcel
    cC
    cS
    wcel
    cA
    cB
    cC
    cF
    co
    cG
    co
    cA
    cB
    cG
    co
    cA
    cC
    cG
    co
    cH
    co
    wceq
    wph
    id
    caovdid.2
    caovdid.3
    caovdid.4
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
    caovdig.1
    caovdig
    syl13anc
end
