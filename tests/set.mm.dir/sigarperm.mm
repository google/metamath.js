include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cmin.mm"
include "caddc.mm"
include "cneg.mm"
include "simp2.mm"
include "simp3.mm"
include "wa.mm"
include "sigarim.mm"
include "recnd.mm"
include "syl2anc.mm"
include "simp1.mm"
include "negsubd.mm"
include "wceq.mm"
include "sigarac.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "sigarexp.mm"
include "3comr.mm"
include "cr.mm"
include "sub32d.mm"
include "addcomd.mm"
include "3eqtr2rd.mm"
include "3eqtrd.mm"
include "3eqtr4rd.mm"

theorem sigarperm
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let vk: setvar k
  assume sigar: |- G = ( x e. CC , y e. CC |-> ( Im ` ( ( * ` x ) x. y ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint k x
  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A - C ) G ( B - C ) ) = ( ( B - A ) G ( C - A ) ) )

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
    cB
    cC
    cG
    co
    #
    cB
    cA
    cG
    co
    #
    cmin
    co
    #
    cA
    cC
    cG
    co
    #
    cmin
    co
    #
    @4
    cA
    cB
    cG
    co
    #
    caddc
    co
    #
    @7
    cmin
    co
    #
    cB
    cA
    cmin
    co
    cC
    cA
    cmin
    co
    cG
    co
    #
    cA
    cC
    cmin
    co
    cB
    cC
    cmin
    co
    cG
    co
    #
    @3
    @6
    @10
    @7
    cmin
    @3
    @4
    @5
    cneg
    #
    caddc
    co
    @6
    @10
    @3
    @4
    @5
    @3
    @1
    @2
    @4
    cc
    wcel
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp3
    #
    @1
    @2
    wa
    @4
    vx
    vy
    cB
    cC
    cG
    sigar
    sigarim
    recnd
    syl2anc
    #
    @3
    @1
    @0
    @5
    cc
    wcel
    @15
    @0
    @1
    @2
    simp1
    #
    @1
    @0
    wa
    @5
    vx
    vy
    cB
    cA
    cG
    sigar
    sigarim
    recnd
    syl2anc
    negsubd
    @3
    @14
    @9
    @4
    caddc
    @3
    @9
    @14
    @3
    @0
    @1
    @9
    @14
    wceq
    @18
    @15
    vx
    vy
    cA
    cB
    cG
    sigar
    sigarac
    syl2anc
    eqcomd
    oveq2d
    eqtr3d
    oveq1d
    @1
    @2
    @0
    @12
    @8
    wceq
    vx
    vy
    cB
    cC
    cA
    cG
    sigar
    sigarexp
    3comr
    @3
    @13
    @9
    @7
    cmin
    co
    cC
    cB
    cG
    co
    #
    cmin
    co
    @9
    @19
    cmin
    co
    #
    @7
    cmin
    co
    @11
    vx
    vy
    cA
    cB
    cC
    cG
    sigar
    sigarexp
    @3
    @9
    @7
    @19
    @3
    @9
    @3
    @0
    @1
    @9
    cr
    wcel
    @18
    @15
    vx
    vy
    cA
    cB
    cG
    sigar
    sigarim
    syl2anc
    recnd
    #
    @3
    @7
    @3
    @0
    @2
    @7
    cr
    wcel
    @18
    @16
    vx
    vy
    cA
    cC
    cG
    sigar
    sigarim
    syl2anc
    recnd
    @3
    @19
    @3
    @2
    @1
    @19
    cr
    wcel
    @16
    @15
    vx
    vy
    cC
    cB
    cG
    sigar
    sigarim
    syl2anc
    recnd
    #
    sub32d
    @3
    @20
    @10
    @7
    cmin
    @3
    @10
    @9
    @4
    caddc
    co
    @9
    @19
    cneg
    #
    caddc
    co
    @20
    @3
    @4
    @9
    @17
    @21
    addcomd
    @3
    @23
    @4
    @9
    caddc
    @3
    @4
    @23
    @3
    @1
    @2
    @4
    @23
    wceq
    @15
    @16
    vx
    vy
    cB
    cC
    cG
    sigar
    sigarac
    syl2anc
    eqcomd
    oveq2d
    @3
    @9
    @19
    @21
    @22
    negsubd
    3eqtr2rd
    oveq1d
    3eqtrd
    3eqtr4rd
end
