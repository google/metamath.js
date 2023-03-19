include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "id.mm"
include "caovcomg.mm"
include "syl12anc.mm"

theorem caovcomd
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
  assume caovcomd.2: |- ( ph -> A e. S )
  assume caovcomd.3: |- ( ph -> B e. S )

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
  assert |- ( ph -> ( A F B ) = ( B F A ) )

  proof
    wph
    wph
    cA
    cS
    wcel
    cB
    cS
    wcel
    cA
    cB
    cF
    co
    cB
    cA
    cF
    co
    wceq
    wph
    id
    caovcomd.2
    caovcomd.3
    wph
    vx
    vy
    cA
    cB
    cS
    cF
    caovcomg.1
    caovcomg
    syl12anc
end
