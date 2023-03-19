include "cprb.mm"
include "wcel.mm"
include "cdm.mm"
include "w3a.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cop.mm"
include "ccprob.mm"
include "cmul.mm"
include "co.mm"
include "cin.mm"
include "cdiv.mm"
include "wceq.mm"
include "cndprobval.mm"
include "oveq1d.mm"
include "adantr.mm"
include "cc.mm"
include "c1.mm"
include "cicc.mm"
include "unitsscn.mm"
include "simp1.mm"
include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "domprobsiga.mm"
include "inelsiga.mm"
include "syl3an1.mm"
include "prob01.mm"
include "syl2anc.mm"
include "sseldi.mm"
include "3adant2.mm"
include "simpr.mm"
include "divcan1d.mm"
include "eqtrd.mm"

theorem cndprobin
  let cA: class A
  let cB: class B
  let cP: class P


  assert |- ( ( ( P e. Prob /\ A e. dom P /\ B e. dom P ) /\ ( P ` B ) =/= 0 ) -> ( ( ( cprob ` P ) ` <. A , B >. ) x. ( P ` B ) ) = ( P ` ( A i^i B ) ) )

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
    cB
    cP
    cfv
    #
    cc0
    wne
    #
    wa
    #
    cA
    cB
    cop
    cP
    ccprob
    cfv
    cfv
    #
    @5
    cmul
    co
    #
    cA
    cB
    cin
    #
    cP
    cfv
    #
    @5
    cdiv
    co
    #
    @5
    cmul
    co
    #
    @11
    @4
    @9
    @13
    wceq
    @6
    @4
    @8
    @12
    @5
    cmul
    cA
    cB
    cP
    cndprobval
    oveq1d
    adantr
    @7
    @11
    @5
    @4
    @11
    cc
    wcel
    @6
    @4
    cc0
    c1
    cicc
    co
    #
    cc
    @11
    unitsscn
    @4
    @0
    @10
    @1
    wcel
    #
    @11
    @14
    wcel
    @0
    @2
    @3
    simp1
    @0
    @1
    csiga
    crn
    cuni
    wcel
    @2
    @3
    @15
    cP
    domprobsiga
    cA
    cB
    @1
    inelsiga
    syl3an1
    @10
    cP
    prob01
    syl2anc
    sseldi
    adantr
    @4
    @5
    cc
    wcel
    @6
    @4
    @14
    cc
    @5
    unitsscn
    @0
    @3
    @5
    @14
    wcel
    @2
    cB
    cP
    prob01
    3adant2
    sseldi
    adantr
    @4
    @6
    simpr
    divcan1d
    eqtrd
end
