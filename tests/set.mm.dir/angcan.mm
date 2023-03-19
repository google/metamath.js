include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "clog.mm"
include "cfv.mm"
include "cim.mm"
include "simp2l.mm"
include "simp1l.mm"
include "simp3l.mm"
include "simp1r.mm"
include "simp3r.mm"
include "divcan5d.mm"
include "fveq2d.mm"
include "wceq.mm"
include "mulcld.mm"
include "mulne0d.mm"
include "simp2r.mm"
include "angval.mm"
include "syl22anc.mm"
include "3adant3.mm"
include "3eqtr4d.mm"

theorem angcan
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume ang.1: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) /\ ( C e. CC /\ C =/= 0 ) ) -> ( ( C x. A ) F ( C x. B ) ) = ( A F B ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    cC
    cc
    wcel
    #
    cC
    cc0
    wne
    #
    wa
    #
    w3a
    #
    cC
    cB
    cmul
    co
    #
    cC
    cA
    cmul
    co
    #
    cdiv
    co
    #
    clog
    cfv
    #
    cim
    cfv
    #
    cB
    cA
    cdiv
    co
    #
    clog
    cfv
    #
    cim
    cfv
    #
    @11
    @10
    cF
    co
    #
    cA
    cB
    cF
    co
    #
    @9
    @13
    @16
    cim
    @9
    @12
    @15
    clog
    @9
    cB
    cA
    cC
    @2
    @3
    @4
    @8
    simp2l
    #
    @0
    @1
    @5
    @8
    simp1l
    #
    @2
    @5
    @6
    @7
    simp3l
    #
    @0
    @1
    @5
    @8
    simp1r
    #
    @2
    @5
    @6
    @7
    simp3r
    #
    divcan5d
    fveq2d
    fveq2d
    @9
    @11
    cc
    wcel
    @11
    cc0
    wne
    @10
    cc
    wcel
    @10
    cc0
    wne
    @18
    @14
    wceq
    @9
    cC
    cA
    @22
    @21
    mulcld
    @9
    cC
    cA
    @22
    @21
    @24
    @23
    mulne0d
    @9
    cC
    cB
    @22
    @20
    mulcld
    @9
    cC
    cB
    @22
    @20
    @24
    @2
    @3
    @4
    @8
    simp2r
    mulne0d
    vx
    vy
    @11
    @10
    cF
    ang.1
    angval
    syl22anc
    @2
    @5
    @19
    @17
    wceq
    @8
    vx
    vy
    cA
    cB
    cF
    ang.1
    angval
    3adant3
    3eqtr4d
end
