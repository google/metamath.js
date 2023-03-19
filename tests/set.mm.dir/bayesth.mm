include "cprb.mm"
include "wcel.mm"
include "cdm.mm"
include "w3a.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "cop.mm"
include "ccprob.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "c1.mm"
include "cicc.mm"
include "cc.mm"
include "unitsscn.mm"
include "cndprob01.mm"
include "3adant2.mm"
include "sseldi.mm"
include "simp11.mm"
include "simp13.mm"
include "prob01.mm"
include "syl2anc.mm"
include "simp3.mm"
include "divcan4d.mm"
include "cin.mm"
include "incom.mm"
include "fveq2i.mm"
include "wceq.mm"
include "cndprobin.mm"
include "simp12.mm"
include "simp2.mm"
include "syl31anc.mm"
include "3eqtr4a.mm"
include "oveq1d.mm"
include "eqtr3d.mm"

theorem bayesth
  let cA: class A
  let cB: class B
  let cP: class P


  assert |- ( ( ( P e. Prob /\ A e. dom P /\ B e. dom P ) /\ ( P ` A ) =/= 0 /\ ( P ` B ) =/= 0 ) -> ( ( cprob ` P ) ` <. A , B >. ) = ( ( ( ( cprob ` P ) ` <. B , A >. ) x. ( P ` A ) ) / ( P ` B ) ) )

  proof
    cP
    cprb
    wcel
    #
    cA
    cP
    cdm
    #
    wcel
    #
    cB
    @1
    wcel
    #
    w3a
    #
    cA
    cP
    cfv
    #
    cc0
    wne
    #
    cB
    cP
    cfv
    #
    cc0
    wne
    #
    w3a
    #
    cA
    cB
    cop
    cP
    ccprob
    cfv
    #
    cfv
    #
    @7
    cmul
    co
    #
    @7
    cdiv
    co
    @11
    cB
    cA
    cop
    @10
    cfv
    @5
    cmul
    co
    #
    @7
    cdiv
    co
    @9
    @11
    @7
    @9
    cc0
    c1
    cicc
    co
    #
    cc
    @11
    unitsscn
    @4
    @8
    @11
    @14
    wcel
    @6
    cA
    cB
    cP
    cndprob01
    3adant2
    sseldi
    @9
    @14
    cc
    @7
    unitsscn
    @9
    @0
    @3
    @7
    @14
    wcel
    @0
    @2
    @3
    @6
    @8
    simp11
    #
    @0
    @2
    @3
    @6
    @8
    simp13
    #
    cB
    cP
    prob01
    syl2anc
    sseldi
    @4
    @6
    @8
    simp3
    divcan4d
    @9
    @12
    @13
    @7
    cdiv
    @9
    cA
    cB
    cin
    #
    cP
    cfv
    #
    cB
    cA
    cin
    #
    cP
    cfv
    #
    @12
    @13
    @17
    @19
    cP
    cA
    cB
    incom
    fveq2i
    @4
    @8
    @12
    @18
    wceq
    @6
    cA
    cB
    cP
    cndprobin
    3adant2
    @9
    @0
    @3
    @2
    @6
    @13
    @20
    wceq
    @15
    @16
    @0
    @2
    @3
    @6
    @8
    simp12
    @4
    @6
    @8
    simp2
    cB
    cA
    cP
    cndprobin
    syl31anc
    3eqtr4a
    oveq1d
    eqtr3d
end
