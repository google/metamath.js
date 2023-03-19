include "wbr.mm"
include "cv.mm"
include "co.mm"
include "wb.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq12d.mm"
include "bibi2d.mm"
include "wcel.mm"
include "wi.mm"
include "wa.mm"
include "breq1.mm"
include "oveq2.mm"
include "breq1d.mm"
include "bibi12d.mm"
include "breq2.mm"
include "breq2d.mm"
include "sylan9bb.mm"
include "imbi2d.mm"
include "vtocl2.mm"
include "vtoclga.mm"

theorem caovord
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
  let wph: wff ph
  let cG: class G
  let cH: class H
  let cK: class K
  let cT: class T
  assume caovord.1: |- A e. _V
  assume caovord.2: |- B e. _V
  assume caovord.3: |- ( z e. S -> ( x R y <-> ( z F x ) R ( z F y ) ) )

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
  assert |- ( C e. S -> ( A R B <-> ( C F A ) R ( C F B ) ) )

  proof
    cA
    cB
    cR
    wbr
    #
    vz
    cv
    #
    cA
    cF
    co
    #
    @1
    cB
    cF
    co
    #
    cR
    wbr
    #
    wb
    #
    @0
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
    #
    wb
    vz
    cC
    cS
    @1
    cC
    wceq
    #
    @4
    @8
    @0
    @9
    @2
    @6
    @3
    @7
    cR
    @1
    cC
    cA
    cF
    oveq1
    @1
    cC
    cB
    cF
    oveq1
    breq12d
    bibi2d
    @1
    cS
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @1
    @11
    cF
    co
    #
    @1
    @12
    cF
    co
    #
    cR
    wbr
    #
    wb
    #
    wi
    @10
    @5
    wi
    vx
    vy
    cA
    cB
    caovord.1
    caovord.2
    @11
    cA
    wceq
    #
    @12
    cB
    wceq
    #
    wa
    @17
    @5
    @10
    @18
    @17
    cA
    @12
    cR
    wbr
    #
    @2
    @15
    cR
    wbr
    #
    wb
    @19
    @5
    @18
    @13
    @20
    @16
    @21
    @11
    cA
    @12
    cR
    breq1
    @18
    @14
    @2
    @15
    cR
    @11
    cA
    @1
    cF
    oveq2
    breq1d
    bibi12d
    @19
    @20
    @0
    @21
    @4
    @12
    cB
    cA
    cR
    breq2
    @19
    @15
    @3
    @2
    cR
    @12
    cB
    @1
    cF
    oveq2
    breq2d
    bibi12d
    sylan9bb
    imbi2d
    caovord.3
    vtocl2
    vtoclga
end
