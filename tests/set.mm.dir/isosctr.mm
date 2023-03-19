include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "cneg.mm"
include "cc0.mm"
include "simp11.mm"
include "simp13.mm"
include "subcld.mm"
include "simp12.mm"
include "simp21.mm"
include "subne0d.mm"
include "simp22.mm"
include "simp23.mm"
include "wb.mm"
include "subcan2.mm"
include "3ad2ant1.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "simp3.mm"
include "isosctrlem3.mm"
include "syl231anc.mm"
include "negsubdi2d.mm"
include "nnncan2d.mm"
include "oveq12d.mm"
include "3eqtr3d.mm"

theorem isosctr
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume isosctrlem3.1: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ( ( A e. CC /\ B e. CC /\ C e. CC ) /\ ( A =/= C /\ B =/= C /\ A =/= B ) /\ ( abs ` ( A - C ) ) = ( abs ` ( B - C ) ) ) -> ( ( C - A ) F ( B - A ) ) = ( ( A - B ) F ( C - B ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    w3a
    #
    cA
    cC
    wne
    #
    cB
    cC
    wne
    #
    cA
    cB
    wne
    #
    w3a
    #
    cA
    cC
    cmin
    co
    #
    cabs
    cfv
    cB
    cC
    cmin
    co
    #
    cabs
    cfv
    wceq
    #
    w3a
    #
    @8
    cneg
    #
    @9
    @8
    cmin
    co
    #
    cF
    co
    #
    @8
    @9
    cmin
    co
    #
    @9
    cneg
    #
    cF
    co
    #
    cC
    cA
    cmin
    co
    #
    cB
    cA
    cmin
    co
    #
    cF
    co
    cA
    cB
    cmin
    co
    #
    cC
    cB
    cmin
    co
    #
    cF
    co
    @11
    @8
    cc
    wcel
    @9
    cc
    wcel
    @8
    cc0
    wne
    @9
    cc0
    wne
    @8
    @9
    wne
    #
    @10
    @14
    @17
    wceq
    @11
    cA
    cC
    @0
    @1
    @2
    @7
    @10
    simp11
    #
    @0
    @1
    @2
    @7
    @10
    simp13
    #
    subcld
    @11
    cB
    cC
    @0
    @1
    @2
    @7
    @10
    simp12
    #
    @24
    subcld
    @11
    cA
    cC
    @23
    @24
    @3
    @4
    @5
    @6
    @10
    simp21
    subne0d
    @11
    cB
    cC
    @25
    @24
    @3
    @4
    @5
    @6
    @10
    simp22
    subne0d
    @11
    @22
    @6
    @3
    @4
    @5
    @6
    @10
    simp23
    @11
    @8
    @9
    cA
    cB
    @3
    @7
    @8
    @9
    wceq
    cA
    cB
    wceq
    wb
    @10
    cA
    cB
    cC
    subcan2
    3ad2ant1
    necon3bid
    mpbird
    @3
    @7
    @10
    simp3
    vx
    vy
    @8
    @9
    cF
    isosctrlem3.1
    isosctrlem3
    syl231anc
    @11
    @12
    @18
    @13
    @19
    cF
    @11
    cA
    cC
    @23
    @24
    negsubdi2d
    @11
    cB
    cA
    cC
    @25
    @23
    @24
    nnncan2d
    oveq12d
    @11
    @15
    @20
    @16
    @21
    cF
    @11
    cA
    cB
    cC
    @23
    @25
    @24
    nnncan2d
    @11
    cB
    cC
    @25
    @24
    negsubdi2d
    oveq12d
    3eqtr3d
end
