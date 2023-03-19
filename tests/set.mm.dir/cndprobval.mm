include "cprb.mm"
include "wcel.mm"
include "cdm.mm"
include "w3a.mm"
include "cop.mm"
include "ccprob.mm"
include "cfv.mm"
include "co.mm"
include "cin.mm"
include "cdiv.mm"
include "df-ov.mm"
include "cv.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "cmpt.mm"
include "df-cndprob.mm"
include "a1i.mm"
include "dmeq.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "mpt2eq123dv.mm"
include "adantl.mm"
include "id.mm"
include "dmexg.mm"
include "mpt2exga.mm"
include "syl2anc.mm"
include "fvmptd.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "simprl.mm"
include "simprr.mm"
include "ineq12d.mm"
include "fveq2d.mm"
include "simp2.mm"
include "simp3.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "syl5eqr.mm"

theorem cndprobval
  let cA: class A
  let cB: class B
  let cP: class P
  let va: setvar a
  let vb: setvar b
  let vp: setvar p


  assert |- ( ( P e. Prob /\ A e. dom P /\ B e. dom P ) -> ( ( cprob ` P ) ` <. A , B >. ) = ( ( P ` ( A i^i B ) ) / ( P ` B ) ) )

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
    cB
    cop
    cP
    ccprob
    cfv
    #
    cfv
    cA
    cB
    @5
    co
    cA
    cB
    cin
    #
    cP
    cfv
    #
    cB
    cP
    cfv
    #
    cdiv
    co
    #
    cA
    cB
    @5
    df-ov
    @4
    va
    vb
    cA
    cB
    @1
    @1
    va
    cv
    #
    vb
    cv
    #
    cin
    #
    cP
    cfv
    #
    @11
    cP
    cfv
    #
    cdiv
    co
    #
    @9
    @5
    cvv
    @0
    @2
    @5
    va
    vb
    @1
    @1
    @15
    cmpt2
    #
    wceq
    @3
    @0
    vp
    cP
    va
    vb
    vp
    cv
    #
    cdm
    #
    @18
    @12
    @17
    cfv
    #
    @11
    @17
    cfv
    #
    cdiv
    co
    #
    cmpt2
    #
    @16
    cprb
    ccprob
    cvv
    ccprob
    vp
    cprb
    @22
    cmpt
    wceq
    @0
    vp
    va
    vb
    df-cndprob
    a1i
    @17
    cP
    wceq
    #
    @22
    @16
    wceq
    @0
    @23
    va
    vb
    @18
    @18
    @21
    @1
    @1
    @15
    @17
    cP
    dmeq
    #
    @24
    @23
    @19
    @13
    @20
    @14
    cdiv
    @12
    @17
    cP
    fveq1
    @11
    @17
    cP
    fveq1
    oveq12d
    mpt2eq123dv
    adantl
    @0
    id
    @0
    @1
    cvv
    wcel
    #
    @25
    @16
    cvv
    wcel
    cP
    cprb
    dmexg
    #
    @26
    va
    vb
    @1
    @1
    @15
    cvv
    cvv
    mpt2exga
    syl2anc
    fvmptd
    3ad2ant1
    @4
    @10
    cA
    wceq
    #
    @11
    cB
    wceq
    #
    wa
    wa
    #
    @13
    @7
    @14
    @8
    cdiv
    @29
    @12
    @6
    cP
    @29
    @10
    cA
    @11
    cB
    @4
    @27
    @28
    simprl
    @4
    @27
    @28
    simprr
    #
    ineq12d
    fveq2d
    @29
    @11
    cB
    cP
    @30
    fveq2d
    oveq12d
    @0
    @2
    @3
    simp2
    @0
    @2
    @3
    simp3
    @4
    @7
    @8
    cdiv
    ovexd
    ovmpt2d
    syl5eqr
end
