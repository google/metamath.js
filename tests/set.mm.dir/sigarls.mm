include "cc.mm"
include "wcel.mm"
include "cr.mm"
include "w3a.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cim.mm"
include "simp1.mm"
include "cjcld.mm"
include "simp2.mm"
include "wa.mm"
include "simpr.mm"
include "recnd.mm"
include "3adant1.mm"
include "mulassd.mm"
include "fveq2d.mm"
include "simp3.mm"
include "mulcld.mm"
include "immul2d.mm"
include "mulcomd.mm"
include "imcl.mm"
include "syl.mm"
include "3eqtr4d.mm"
include "eqtr3d.mm"
include "wceq.mm"
include "simpl.mm"
include "sigarval.mm"
include "syl2anc.mm"
include "3adant3.mm"
include "oveq1d.mm"

theorem sigarls
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
  assert |- ( ( A e. CC /\ B e. CC /\ C e. RR ) -> ( A G ( B x. C ) ) = ( ( A G B ) x. C ) )

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
    cr
    wcel
    #
    w3a
    #
    cA
    ccj
    cfv
    #
    cB
    cC
    cmul
    co
    #
    cmul
    co
    #
    cim
    cfv
    #
    @4
    cB
    cmul
    co
    #
    cim
    cfv
    #
    cC
    cmul
    co
    #
    cA
    @5
    cG
    co
    #
    cA
    cB
    cG
    co
    #
    cC
    cmul
    co
    @3
    @8
    cC
    cmul
    co
    #
    cim
    cfv
    #
    @7
    @10
    @3
    @13
    @6
    cim
    @3
    @4
    cB
    cC
    @3
    cA
    @0
    @1
    @2
    simp1
    #
    cjcld
    #
    @0
    @1
    @2
    simp2
    #
    @1
    @2
    cC
    cc
    wcel
    @0
    @1
    @2
    wa
    #
    cC
    @1
    @2
    simpr
    recnd
    #
    3adant1
    #
    mulassd
    fveq2d
    @3
    cC
    @8
    cmul
    co
    #
    cim
    cfv
    cC
    @9
    cmul
    co
    @14
    @10
    @3
    cC
    @8
    @0
    @1
    @2
    simp3
    @3
    @4
    cB
    @16
    @17
    mulcld
    #
    immul2d
    @3
    @13
    @21
    cim
    @3
    @8
    cC
    @22
    @20
    mulcomd
    fveq2d
    @3
    @9
    cC
    @3
    @8
    cc
    wcel
    #
    @9
    cc
    wcel
    @22
    @23
    @9
    @8
    imcl
    recnd
    syl
    @20
    mulcomd
    3eqtr4d
    eqtr3d
    @3
    @0
    @5
    cc
    wcel
    #
    @11
    @7
    wceq
    @15
    @1
    @2
    @24
    @0
    @18
    cB
    cC
    @1
    @2
    simpl
    @19
    mulcld
    3adant1
    vx
    vy
    cA
    @5
    cG
    sigar
    sigarval
    syl2anc
    @3
    @12
    @9
    cC
    cmul
    @0
    @1
    @12
    @9
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
    oveq1d
    3eqtr4d
end
