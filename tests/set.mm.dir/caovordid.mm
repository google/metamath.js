include "wcel.mm"
include "wbr.mm"
include "co.mm"
include "wi.mm"
include "id.mm"
include "caovordig.mm"
include "syl13anc.mm"

theorem caovordid
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let cD: class D
  let cG: class G
  let cH: class H
  let cK: class K
  let cT: class T
  assume caovordig.1: |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( x R y -> ( z F x ) R ( z F y ) ) )
  assume caovordid.2: |- ( ph -> A e. S )
  assume caovordid.3: |- ( ph -> B e. S )
  assume caovordid.4: |- ( ph -> C e. S )

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
  disjoint R x
  disjoint R y
  disjoint R z
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
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ph -> ( A R B -> ( C F A ) R ( C F B ) ) )

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
    cR
    wbr
    cC
    cA
    cF
    co
    cC
    cB
    cF
    co
    cR
    wbr
    wi
    wph
    id
    caovordid.2
    caovordid.3
    caovordid.4
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    cR
    cS
    cF
    caovordig.1
    caovordig
    syl13anc
end
