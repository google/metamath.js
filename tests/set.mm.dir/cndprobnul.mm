include "cprb.mm"
include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "c0.mm"
include "cop.mm"
include "ccprob.mm"
include "cin.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "nuleldmp.mm"
include "syl.mm"
include "simp2.mm"
include "cndprobval.mm"
include "syl3anc.mm"
include "0in.mm"
include "fveq2i.mm"
include "oveq1i.mm"
include "a1i.mm"
include "probnul.mm"
include "oveq1d.mm"
include "c1.mm"
include "cicc.mm"
include "cc.mm"
include "prob01.mm"
include "3adant3.mm"
include "elunitcn.mm"
include "simp3.mm"
include "div0d.mm"
include "3eqtrd.mm"
include "eqtrd.mm"

theorem cndprobnul
  let cA: class A
  let cP: class P


  assert |- ( ( P e. Prob /\ A e. dom P /\ ( P ` A ) =/= 0 ) -> ( ( cprob ` P ) ` <. (/) , A >. ) = 0 )

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
    cA
    cP
    cfv
    #
    cc0
    wne
    #
    w3a
    #
    c0
    cA
    cop
    cP
    ccprob
    cfv
    cfv
    #
    c0
    cA
    cin
    #
    cP
    cfv
    #
    @3
    cdiv
    co
    #
    cc0
    @5
    @0
    c0
    @1
    wcel
    #
    @2
    @6
    @9
    wceq
    @0
    @2
    @4
    simp1
    #
    @5
    @0
    @10
    @11
    cP
    nuleldmp
    syl
    @0
    @2
    @4
    simp2
    c0
    cA
    cP
    cndprobval
    syl3anc
    @5
    @9
    c0
    cP
    cfv
    #
    @3
    cdiv
    co
    #
    cc0
    @3
    cdiv
    co
    cc0
    @9
    @13
    wceq
    @5
    @8
    @12
    @3
    cdiv
    @7
    c0
    cP
    cA
    0in
    fveq2i
    oveq1i
    a1i
    @5
    @12
    cc0
    @3
    cdiv
    @5
    @0
    @12
    cc0
    wceq
    @11
    cP
    probnul
    syl
    oveq1d
    @5
    @3
    @5
    @3
    cc0
    c1
    cicc
    co
    wcel
    #
    @3
    cc
    wcel
    @0
    @2
    @14
    @4
    cA
    cP
    prob01
    3adant3
    @3
    elunitcn
    syl
    @0
    @2
    @4
    simp3
    div0d
    3eqtrd
    eqtrd
end
