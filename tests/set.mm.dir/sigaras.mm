include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "cneg.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "addcld.mm"
include "sigarac.mm"
include "syl2anc.mm"
include "sigaraf.mm"
include "negeqd.mm"
include "3com12.mm"
include "wa.mm"
include "cr.mm"
include "3simpa.mm"
include "ancomd.mm"
include "sigarim.mm"
include "syl.mm"
include "recnd.mm"
include "3simpb.mm"
include "negdid.mm"
include "eqtrd.mm"
include "eqcomd.mm"
include "oveq12d.mm"
include "3eqtrd.mm"

theorem sigaras
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
  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( A G ( B + C ) ) = ( ( A G B ) + ( A G C ) ) )

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
    cB
    cC
    caddc
    co
    #
    cG
    co
    #
    @4
    cA
    cG
    co
    #
    cneg
    #
    cB
    cA
    cG
    co
    #
    cneg
    #
    cC
    cA
    cG
    co
    #
    cneg
    #
    caddc
    co
    #
    cA
    cB
    cG
    co
    #
    cA
    cC
    cG
    co
    #
    caddc
    co
    @3
    @0
    @4
    cc
    wcel
    @5
    @7
    wceq
    @0
    @1
    @2
    simp1
    #
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
    addcld
    vx
    vy
    cA
    @4
    cG
    sigar
    sigarac
    syl2anc
    @3
    @7
    @8
    @10
    caddc
    co
    #
    cneg
    #
    @12
    @1
    @0
    @2
    @7
    @19
    wceq
    @1
    @0
    @2
    w3a
    @6
    @18
    vx
    vy
    cB
    cA
    cC
    cG
    sigar
    sigaraf
    negeqd
    3com12
    @3
    @8
    @10
    @3
    @8
    @3
    @1
    @0
    wa
    @8
    cr
    wcel
    @3
    @0
    @1
    @0
    @1
    @2
    3simpa
    ancomd
    vx
    vy
    cB
    cA
    cG
    sigar
    sigarim
    syl
    recnd
    @3
    @10
    @3
    @2
    @0
    wa
    @10
    cr
    wcel
    @3
    @0
    @2
    @0
    @1
    @2
    3simpb
    ancomd
    vx
    vy
    cC
    cA
    cG
    sigar
    sigarim
    syl
    recnd
    negdid
    eqtrd
    @3
    @9
    @13
    @11
    @14
    caddc
    @3
    @13
    @9
    @3
    @0
    @1
    @13
    @9
    wceq
    @15
    @16
    vx
    vy
    cA
    cB
    cG
    sigar
    sigarac
    syl2anc
    eqcomd
    @3
    @14
    @11
    @3
    @0
    @2
    @14
    @11
    wceq
    @15
    @17
    vx
    vy
    cA
    cC
    cG
    sigar
    sigarac
    syl2anc
    eqcomd
    oveq12d
    3eqtrd
end
