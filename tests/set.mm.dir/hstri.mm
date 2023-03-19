include "cv.mm"
include "cfv.mm"
include "cno.mm"
include "c1.mm"
include "wceq.mm"
include "wi.mm"
include "chst.mm"
include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "wss.mm"
include "dfral2.mm"
include "cdif.mm"
include "strlem1.mm"
include "wcel.mm"
include "wa.mm"
include "cch.mm"
include "cpjh.mm"
include "cmpt.mm"
include "eqid.mm"
include "biid.mm"
include "hstrlem3.mm"
include "hstrlem6.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "notbid.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimiva.mm"
include "syl.mm"
include "con1i.mm"
include "sylbi.mm"

theorem hstri
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vu: setvar u
  let vx: setvar x
  assume hstr.1: |- A e. CH
  assume hstr.2: |- B e. CH

  disjoint A f
  disjoint B f
  disjoint u x
  disjoint f x
  disjoint A x
  disjoint f u
  disjoint A u
  disjoint B x
  disjoint B u
  assert |- ( A. f e. CHStates ( ( normh ` ( f ` A ) ) = 1 -> ( normh ` ( f ` B ) ) = 1 ) -> A C_ B )

  proof
    cA
    vf
    cv
    #
    cfv
    #
    cno
    cfv
    #
    c1
    wceq
    #
    cB
    @0
    cfv
    #
    cno
    cfv
    #
    c1
    wceq
    #
    wi
    #
    vf
    chst
    wral
    @7
    wn
    #
    vf
    chst
    wrex
    #
    wn
    cA
    cB
    wss
    #
    @7
    vf
    chst
    dfral2
    @10
    @9
    @10
    wn
    vu
    cv
    #
    cno
    cfv
    c1
    wceq
    #
    vu
    cA
    cB
    cdif
    #
    wrex
    @9
    vu
    cA
    cB
    hstr.1
    hstr.2
    strlem1
    @12
    @9
    vu
    @13
    @11
    @13
    wcel
    @12
    wa
    #
    vx
    cch
    @11
    vx
    cv
    cpjh
    cfv
    cfv
    cmpt
    #
    chst
    wcel
    cA
    @15
    cfv
    #
    cno
    cfv
    #
    c1
    wceq
    #
    cB
    @15
    cfv
    #
    cno
    cfv
    #
    c1
    wceq
    #
    wi
    #
    wn
    #
    @9
    @14
    vx
    vu
    cA
    cB
    @15
    @15
    eqid
    #
    @14
    biid
    #
    hstr.1
    hstr.2
    hstrlem3
    @14
    vx
    vu
    cA
    cB
    @15
    @24
    @25
    hstr.1
    hstr.2
    hstrlem6
    @8
    @23
    vf
    @15
    chst
    @0
    @15
    wceq
    #
    @7
    @22
    @26
    @3
    @18
    @6
    @21
    @26
    @2
    @17
    c1
    @26
    @1
    @16
    cno
    cA
    @0
    @15
    fveq1
    fveq2d
    eqeq1d
    @26
    @5
    @20
    c1
    @26
    @4
    @19
    cno
    cB
    @0
    @15
    fveq1
    fveq2d
    eqeq1d
    imbi12d
    notbid
    rspcev
    syl2anc
    rexlimiva
    syl
    con1i
    sylbi
end
