include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "cim.mm"
include "wceq.mm"
include "wa.mm"
include "cjsub.mm"
include "oveq1d.mm"
include "3adant2.mm"
include "simp1.mm"
include "cjcld.mm"
include "simp3.mm"
include "simp2.mm"
include "subdird.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "mulcld.mm"
include "imsubd.mm"
include "subcld.mm"
include "sigarval.mm"
include "syl2anc.mm"
include "3adant3.mm"
include "3simpc.mm"
include "ancomd.mm"
include "syl.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem sigarmf
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
  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A - C ) G B ) = ( ( A G B ) - ( C G B ) ) )

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
    #
    ccj
    cfv
    #
    cB
    cmul
    co
    #
    cim
    cfv
    #
    cA
    ccj
    cfv
    #
    cB
    cmul
    co
    #
    cim
    cfv
    #
    cC
    ccj
    cfv
    #
    cB
    cmul
    co
    #
    cim
    cfv
    #
    cmin
    co
    #
    @4
    cB
    cG
    co
    #
    cA
    cB
    cG
    co
    #
    cC
    cB
    cG
    co
    #
    cmin
    co
    @3
    @7
    @9
    @12
    cmin
    co
    #
    cim
    cfv
    @14
    @3
    @6
    @18
    cim
    @3
    @6
    @8
    @11
    cmin
    co
    #
    cB
    cmul
    co
    #
    @18
    @0
    @2
    @6
    @20
    wceq
    @1
    @0
    @2
    wa
    @5
    @19
    cB
    cmul
    cA
    cC
    cjsub
    oveq1d
    3adant2
    @3
    @8
    @11
    cB
    @3
    cA
    @0
    @1
    @2
    simp1
    #
    cjcld
    #
    @3
    cC
    @0
    @1
    @2
    simp3
    #
    cjcld
    #
    @0
    @1
    @2
    simp2
    #
    subdird
    eqtrd
    fveq2d
    @3
    @9
    @12
    @3
    @8
    cB
    @22
    @25
    mulcld
    @3
    @11
    cB
    @24
    @25
    mulcld
    imsubd
    eqtrd
    @3
    @4
    cc
    wcel
    @1
    @15
    @7
    wceq
    @3
    cA
    cC
    @21
    @23
    subcld
    @25
    vx
    vy
    @4
    cB
    cG
    sigar
    sigarval
    syl2anc
    @3
    @16
    @10
    @17
    @13
    cmin
    @0
    @1
    @16
    @10
    wceq
    @2
    vx
    vy
    cA
    cB
    cG
    sigar
    sigarval
    3adant3
    @3
    @2
    @1
    wa
    @17
    @13
    wceq
    @3
    @1
    @2
    @0
    @1
    @2
    3simpc
    ancomd
    vx
    vy
    cC
    cB
    cG
    sigar
    sigarval
    syl
    oveq12d
    3eqtr4d
end
