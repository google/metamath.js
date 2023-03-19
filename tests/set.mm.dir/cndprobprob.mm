include "cprb.mm"
include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cop.mm"
include "ccprob.mm"
include "cmpt.mm"
include "cin.mm"
include "cdiv.mm"
include "co.mm"
include "cmeas.mm"
include "crp.mm"
include "domprobmeas.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "c1.mm"
include "cicc.mm"
include "cr.mm"
include "prob01.mm"
include "3adant3.mm"
include "elunitrn.mm"
include "syl.mm"
include "cle.mm"
include "wbr.mm"
include "elunitge0.mm"
include "simp3.mm"
include "ne0gt0d.mm"
include "elrpd.mm"
include "probmeasb.mm"
include "syl3anc.mm"
include "wb.mm"
include "wa.mm"
include "wceq.mm"
include "3anan32.mm"
include "cndprobval.mm"
include "sylbir.mm"
include "mpteq2dva.mm"
include "eleq1d.mm"
include "mpbird.mm"

theorem cndprobprob
  let cB: class B
  let cP: class P
  let va: setvar a

  disjoint B a
  disjoint P a
  assert |- ( ( P e. Prob /\ B e. dom P /\ ( P ` B ) =/= 0 ) -> ( a e. dom P |-> ( ( cprob ` P ) ` <. a , B >. ) ) e. Prob )

  proof
    cP
    cprb
    wcel
    #
    cB
    cP
    cdm
    #
    wcel
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
    va
    @1
    va
    cv
    #
    cB
    cop
    cP
    ccprob
    cfv
    cfv
    #
    cmpt
    #
    cprb
    wcel
    #
    va
    @1
    @6
    cB
    cin
    cP
    cfv
    @3
    cdiv
    co
    #
    cmpt
    #
    cprb
    wcel
    #
    @5
    cP
    @1
    cmeas
    cfv
    wcel
    #
    @2
    @3
    crp
    wcel
    @12
    @0
    @2
    @13
    @4
    cP
    domprobmeas
    3ad2ant1
    @0
    @2
    @4
    simp2
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
    cr
    wcel
    @0
    @2
    @14
    @4
    cB
    cP
    prob01
    3adant3
    #
    @3
    elunitrn
    syl
    #
    @5
    @3
    @16
    @5
    @14
    cc0
    @3
    cle
    wbr
    @15
    @3
    elunitge0
    syl
    @0
    @2
    @4
    simp3
    ne0gt0d
    elrpd
    va
    cB
    @1
    cP
    probmeasb
    syl3anc
    @0
    @2
    @9
    @12
    wb
    @4
    @0
    @2
    wa
    #
    @8
    @11
    cprb
    @17
    va
    @1
    @7
    @10
    @17
    @6
    @1
    wcel
    #
    wa
    @0
    @18
    @2
    w3a
    @7
    @10
    wceq
    @0
    @18
    @2
    3anan32
    @6
    cB
    cP
    cndprobval
    sylbir
    mpteq2dva
    eleq1d
    3adant3
    mpbird
end
