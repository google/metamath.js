include "co.mm"
include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "breq1.mm"
include "caovord2d.mm"
include "caovordd.mm"
include "bibi12d.mm"
include "syl5ibr.mm"

theorem caovord3d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cT: class T
  assume caovordg.1: |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( x R y <-> ( z F x ) R ( z F y ) ) )
  assume caovordd.2: |- ( ph -> A e. S )
  assume caovordd.3: |- ( ph -> B e. S )
  assume caovordd.4: |- ( ph -> C e. S )
  assume caovord2d.com: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) )
  assume caovord3d.5: |- ( ph -> D e. S )

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
  disjoint D x
  disjoint D y
  disjoint D z
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
  assert |- ( ph -> ( ( A F B ) = ( C F D ) -> ( A R C <-> D R B ) ) )

  proof
    cA
    cB
    cF
    co
    #
    cC
    cD
    cF
    co
    #
    wceq
    cA
    cC
    cR
    wbr
    #
    cD
    cB
    cR
    wbr
    #
    wb
    wph
    @0
    cC
    cB
    cF
    co
    #
    cR
    wbr
    #
    @1
    @4
    cR
    wbr
    #
    wb
    @0
    @1
    @4
    cR
    breq1
    wph
    @2
    @5
    @3
    @6
    wph
    vx
    vy
    vz
    cA
    cC
    cB
    cR
    cS
    cF
    caovordg.1
    caovordd.2
    caovordd.4
    caovordd.3
    caovord2d.com
    caovord2d
    wph
    vx
    vy
    vz
    cD
    cB
    cC
    cR
    cS
    cF
    caovordg.1
    caovord3d.5
    caovordd.3
    caovordd.4
    caovordd
    bibi12d
    syl5ibr
end
