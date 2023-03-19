include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "id.mm"
include "caovassg.mm"
include "syl13anc.mm"

theorem caovassd
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
  assume caovassg.1: |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) )
  assume caovassd.2: |- ( ph -> A e. S )
  assume caovassd.3: |- ( ph -> B e. S )
  assume caovassd.4: |- ( ph -> C e. S )

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
  assert |- ( ph -> ( ( A F B ) F C ) = ( A F ( B F C ) ) )

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
    cS
    wcel
    cA
    cB
    cF
    co
    cC
    cF
    co
    cA
    cB
    cC
    cF
    co
    cF
    co
    wceq
    wph
    id
    caovassd.2
    caovassd.3
    caovassd.4
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    cS
    cF
    caovassg.1
    caovassg
    syl13anc
end
