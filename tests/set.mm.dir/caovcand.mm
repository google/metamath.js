include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "id.mm"
include "caovcang.mm"
include "syl13anc.mm"

theorem caovcand
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
  assert |- ( ph -> ( ( A F B ) = ( A F C ) <-> B = C ) )

  proof
    wph
    wph
    cA
    cT
    wcel
    cB
    cS
    wcel
    cC
    cS
    wcel
    cA
    cB
    cF
    co
    cA
    cC
    cF
    co
    wceq
    cB
    cC
    wceq
    wb
    wph
    id
    caovcand.2
    caovcand.3
    caovcand.4
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
    caovcang
    syl13anc
end
