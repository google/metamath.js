include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "simp2.mm"
include "simp3.mm"
include "subcld.mm"
include "sigarmf.mm"
include "syld3an2.mm"
include "sigarms.mm"
include "oveq1d.mm"
include "cc0.mm"
include "syld3an1.mm"
include "sigarid.mm"
include "syl.mm"
include "oveq2d.mm"
include "wa.mm"
include "sigarim.mm"
include "recnd.mm"
include "syl2anc.mm"
include "subid1d.mm"
include "3eqtrd.mm"

theorem sigarexp
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
  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A - C ) G ( B - C ) ) = ( ( ( A G B ) - ( A G C ) ) - ( C G B ) ) )

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
    cmin
    co
    cB
    cC
    cmin
    co
    #
    cG
    co
    #
    cA
    @4
    cG
    co
    #
    cC
    @4
    cG
    co
    #
    cmin
    co
    #
    cA
    cB
    cG
    co
    cA
    cC
    cG
    co
    cmin
    co
    #
    @7
    cmin
    co
    @9
    cC
    cB
    cG
    co
    #
    cmin
    co
    @0
    @4
    cc
    wcel
    @1
    @2
    @5
    @8
    wceq
    @3
    cB
    cC
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
    subcld
    vx
    vy
    cA
    @4
    cC
    cG
    sigar
    sigarmf
    syld3an2
    @3
    @6
    @9
    @7
    cmin
    vx
    vy
    cA
    cB
    cC
    cG
    sigar
    sigarms
    oveq1d
    @3
    @7
    @10
    @9
    cmin
    @3
    @7
    @10
    cC
    cC
    cG
    co
    #
    cmin
    co
    #
    @10
    cc0
    cmin
    co
    @10
    @2
    @1
    @0
    @2
    @7
    @14
    wceq
    @12
    vx
    vy
    cC
    cB
    cC
    cG
    sigar
    sigarms
    syld3an1
    @3
    @13
    cc0
    @10
    cmin
    @3
    @2
    @13
    cc0
    wceq
    @12
    vx
    vy
    cC
    cG
    sigar
    sigarid
    syl
    oveq2d
    @3
    @10
    @3
    @2
    @1
    @10
    cc
    wcel
    @12
    @11
    @2
    @1
    wa
    @10
    vx
    vy
    cC
    cB
    cG
    sigar
    sigarim
    recnd
    syl2anc
    subid1d
    3eqtrd
    oveq2d
    3eqtrd
end
