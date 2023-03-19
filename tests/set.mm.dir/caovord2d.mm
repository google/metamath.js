include "wbr.mm"
include "co.mm"
include "caovordd.mm"
include "caovcomd.mm"
include "breq12d.mm"
include "bitrd.mm"

theorem caovord2d
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
  assume caovordg.1: |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( x R y <-> ( z F x ) R ( z F y ) ) )
  assume caovordd.2: |- ( ph -> A e. S )
  assume caovordd.3: |- ( ph -> B e. S )
  assume caovordd.4: |- ( ph -> C e. S )
  assume caovord2d.com: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) = ( y F x ) )

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
  assert |- ( ph -> ( A R B <-> ( A F C ) R ( B F C ) ) )

  proof
    wph
    cA
    cB
    cR
    wbr
    cC
    cA
    cF
    co
    #
    cC
    cB
    cF
    co
    #
    cR
    wbr
    cA
    cC
    cF
    co
    #
    cB
    cC
    cF
    co
    #
    cR
    wbr
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
    caovordg.1
    caovordd.2
    caovordd.3
    caovordd.4
    caovordd
    wph
    @0
    @2
    @1
    @3
    cR
    wph
    vx
    vy
    cC
    cA
    cS
    cF
    caovord2d.com
    caovordd.4
    caovordd.2
    caovcomd
    wph
    vx
    vy
    cC
    cB
    cS
    cF
    caovord2d.com
    caovordd.4
    caovordd.3
    caovcomd
    breq12d
    bitrd
end
