include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "caovord2.mm"
include "adantr.mm"
include "breq1.mm"
include "sylan9bb.mm"
include "caovord.mm"
include "ad2antlr.mm"
include "bitr4d.mm"

theorem caovord3
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
  let wph: wff ph
  let cG: class G
  let cH: class H
  let cK: class K
  let cT: class T
  assume caovord.1: |- A e. _V
  assume caovord.2: |- B e. _V
  assume caovord.3: |- ( z e. S -> ( x R y <-> ( z F x ) R ( z F y ) ) )
  assume caovord2.3: |- C e. _V
  assume caovord2.com: |- ( x F y ) = ( y F x )
  assume caovord3.4: |- D e. _V

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
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint ph x
  disjoint ph y
  disjoint ph z
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
  assert |- ( ( ( B e. S /\ C e. S ) /\ ( A F B ) = ( C F D ) ) -> ( A R C <-> D R B ) )

  proof
    cB
    cS
    wcel
    #
    cC
    cS
    wcel
    #
    wa
    #
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
    #
    wa
    cA
    cC
    cR
    wbr
    #
    @4
    cC
    cB
    cF
    co
    #
    cR
    wbr
    #
    cD
    cB
    cR
    wbr
    #
    @2
    @6
    @3
    @7
    cR
    wbr
    #
    @5
    @8
    @0
    @6
    @10
    wb
    @1
    vx
    vy
    vz
    cA
    cC
    cB
    cR
    cS
    cF
    caovord.1
    caovord2.3
    caovord.3
    caovord.2
    caovord2.com
    caovord2
    adantr
    @3
    @4
    @7
    cR
    breq1
    sylan9bb
    @1
    @9
    @8
    wb
    @0
    @5
    vx
    vy
    vz
    cD
    cB
    cC
    cR
    cS
    cF
    caovord3.4
    caovord.2
    caovord.3
    caovord
    ad2antlr
    bitr4d
end
