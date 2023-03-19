include "cprb.mm"
include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cuni.mm"
include "cop.mm"
include "ccprob.mm"
include "cin.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "simpl.mm"
include "unveldomd.mm"
include "simpr.mm"
include "cndprobval.mm"
include "syl3anc.mm"
include "3adant3.mm"
include "wss.mm"
include "elssuni.mm"
include "3ad2ant2.mm"
include "sseqin2.mm"
include "sylib.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "cicc.mm"
include "cc.mm"
include "prob01.mm"
include "elunitcn.mm"
include "syl.mm"
include "simp3.mm"
include "dividd.mm"
include "3eqtrd.mm"

theorem cndprobtot
  let cA: class A
  let cP: class P


  assert |- ( ( P e. Prob /\ A e. dom P /\ ( P ` A ) =/= 0 ) -> ( ( cprob ` P ) ` <. U. dom P , A >. ) = 1 )

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
    @1
    cuni
    #
    cA
    cop
    cP
    ccprob
    cfv
    cfv
    #
    @6
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
    @3
    @3
    cdiv
    co
    c1
    @0
    @2
    @7
    @10
    wceq
    #
    @4
    @0
    @2
    wa
    #
    @0
    @6
    @1
    wcel
    @2
    @11
    @0
    @2
    simpl
    #
    @12
    cP
    @13
    unveldomd
    @0
    @2
    simpr
    @6
    cA
    cP
    cndprobval
    syl3anc
    3adant3
    @5
    @9
    @3
    @3
    cdiv
    @5
    @8
    cA
    cP
    @5
    cA
    @6
    wss
    #
    @8
    cA
    wceq
    @2
    @0
    @14
    @4
    cA
    @1
    elssuni
    3ad2ant2
    cA
    @6
    sseqin2
    sylib
    fveq2d
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
    @15
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
    dividd
    3eqtrd
end
