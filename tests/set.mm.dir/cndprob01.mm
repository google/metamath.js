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
include "cin.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cicc.mm"
include "wceq.mm"
include "cndprobval.mm"
include "adantr.mm"
include "cle.mm"
include "wbr.mm"
include "cmeas.mm"
include "simpl1.mm"
include "domprobmeas.mm"
include "syl.mm"
include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "domprobsiga.mm"
include "simpl2.mm"
include "simpl3.mm"
include "inelsiga.mm"
include "syl3anc.mm"
include "wss.mm"
include "inss2.mm"
include "a1i.mm"
include "measssd.mm"
include "wb.mm"
include "prob01.mm"
include "syl2anc.mm"
include "simpr.mm"
include "unitdivcld.mm"
include "mpbid.mm"
include "eqeltrd.mm"

theorem cndprob01
  let cA: class A
  let cB: class B
  let cP: class P


  assert |- ( ( ( P e. Prob /\ A e. dom P /\ B e. dom P ) /\ ( P ` B ) =/= 0 ) -> ( ( cprob ` P ) ` <. A , B >. ) e. ( 0 [,] 1 ) )

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
    cc0
    c1
    cicc
    co
    #
    @4
    @8
    @11
    wceq
    @6
    cA
    cB
    cP
    cndprobval
    adantr
    @7
    @10
    @5
    cle
    wbr
    #
    @11
    @12
    wcel
    #
    @7
    @9
    cB
    @1
    cP
    @7
    @0
    cP
    @1
    cmeas
    cfv
    wcel
    @0
    @2
    @3
    @6
    simpl1
    #
    cP
    domprobmeas
    syl
    @7
    @1
    csiga
    crn
    cuni
    wcel
    #
    @2
    @3
    @9
    @1
    wcel
    #
    @7
    @0
    @16
    @15
    cP
    domprobsiga
    syl
    @0
    @2
    @3
    @6
    simpl2
    @0
    @2
    @3
    @6
    simpl3
    #
    cA
    cB
    @1
    inelsiga
    syl3anc
    #
    @18
    @9
    cB
    wss
    @7
    cA
    cB
    inss2
    a1i
    measssd
    @7
    @10
    @12
    wcel
    #
    @5
    @12
    wcel
    #
    @6
    @13
    @14
    wb
    @7
    @0
    @17
    @20
    @15
    @19
    @9
    cP
    prob01
    syl2anc
    @7
    @0
    @3
    @21
    @15
    @18
    cB
    cP
    prob01
    syl2anc
    @4
    @6
    simpr
    @10
    @5
    unitdivcld
    syl3anc
    mpbid
    eqeltrd
end
