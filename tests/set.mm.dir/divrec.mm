include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cmul.mm"
include "wceq.mm"
include "simp2.mm"
include "simp1.mm"
include "reccl.mm"
include "3adant1.mm"
include "mul12d.mm"
include "recid.mm"
include "oveq2d.mm"
include "mulid1d.mm"
include "3eqtrd.mm"
include "wa.mm"
include "wb.mm"
include "mulcld.mm"
include "3simpc.mm"
include "divmul.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem divrec
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> ( A / B ) = ( A x. ( 1 / B ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    #
    cA
    cB
    cdiv
    co
    cA
    c1
    cB
    cdiv
    co
    #
    cmul
    co
    #
    wceq
    #
    cB
    @5
    cmul
    co
    #
    cA
    wceq
    #
    @3
    @7
    cA
    cB
    @4
    cmul
    co
    #
    cmul
    co
    cA
    c1
    cmul
    co
    cA
    @3
    cB
    cA
    @4
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp1
    #
    @1
    @2
    @4
    cc
    wcel
    @0
    cB
    reccl
    3adant1
    #
    mul12d
    @3
    @9
    c1
    cA
    cmul
    @1
    @2
    @9
    c1
    wceq
    @0
    cB
    recid
    3adant1
    oveq2d
    @3
    cA
    @10
    mulid1d
    3eqtrd
    @3
    @0
    @5
    cc
    wcel
    @1
    @2
    wa
    @6
    @8
    wb
    @10
    @3
    cA
    @4
    @10
    @11
    mulcld
    @0
    @1
    @2
    3simpc
    cA
    @5
    cB
    divmul
    syl3anc
    mpbird
end
