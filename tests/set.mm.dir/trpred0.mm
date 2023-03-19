include "c0.mm"
include "ctrpred.mm"
include "com.mm"
include "cv.mm"
include "cvv.mm"
include "cpred.mm"
include "ciun.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "cfv.mm"
include "dftrpred2.mm"
include "wcel.mm"
include "wceq.mm"
include "pred0.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "iun0.mm"
include "eqtri.mm"
include "mpteq2i.mm"
include "rdgeq12.mm"
include "mp2an.mm"
include "reseq1i.mm"
include "fveq1i.mm"
include "csuc.mm"
include "wrex.mm"
include "wo.mm"
include "nn0suc.mm"
include "fveq2.mm"
include "0ex.mm"
include "fr0g.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "nfcv.mm"
include "eqid.mm"
include "eqidd.mm"
include "frsucmpt.mm"
include "mpan2.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "jaoi.mm"
include "syl.mm"
include "syl5eq.mm"
include "3eqtri.mm"

theorem trpred0
  let cR: class R
  let cX: class X
  let va: setvar a
  let vi: setvar i
  let vj: setvar j
  let vy: setvar y


  assert |- TrPred ( R , (/) , X ) = (/)

  proof
    c0
    cR
    cX
    ctrpred
    vi
    com
    vi
    cv
    #
    va
    cvv
    vy
    va
    cv
    #
    c0
    cR
    vy
    cv
    #
    cpred
    #
    ciun
    #
    cmpt
    #
    c0
    cR
    cX
    cpred
    #
    crdg
    #
    com
    cres
    #
    cfv
    #
    ciun
    vi
    com
    c0
    ciun
    c0
    vy
    c0
    cR
    vi
    cX
    va
    dftrpred2
    vi
    com
    @9
    c0
    @0
    com
    wcel
    #
    @9
    @0
    va
    cvv
    c0
    cmpt
    #
    c0
    crdg
    #
    com
    cres
    #
    cfv
    #
    c0
    @0
    @8
    @13
    @7
    @12
    com
    @5
    @11
    wceq
    @6
    c0
    wceq
    @7
    @12
    wceq
    va
    cvv
    @4
    c0
    @4
    vy
    @1
    c0
    ciun
    c0
    vy
    @1
    @3
    c0
    @3
    c0
    wceq
    @2
    @1
    wcel
    cR
    @2
    pred0
    a1i
    iuneq2i
    vy
    @1
    iun0
    eqtri
    mpteq2i
    cR
    cX
    pred0
    @6
    c0
    @5
    @11
    rdgeq12
    mp2an
    reseq1i
    fveq1i
    @10
    @0
    c0
    wceq
    #
    @0
    vj
    cv
    #
    csuc
    #
    wceq
    #
    vj
    com
    wrex
    #
    wo
    @14
    c0
    wceq
    #
    vj
    @0
    nn0suc
    @15
    @20
    @19
    @15
    @14
    c0
    @13
    cfv
    #
    c0
    @0
    c0
    @13
    fveq2
    c0
    cvv
    wcel
    #
    @21
    c0
    wceq
    0ex
    c0
    cvv
    @11
    fr0g
    ax-mp
    syl6eq
    @18
    @20
    vj
    com
    @16
    com
    wcel
    #
    @20
    @18
    @17
    @13
    cfv
    #
    c0
    wceq
    #
    @23
    @22
    @25
    0ex
    va
    c0
    @16
    c0
    c0
    @13
    cvv
    va
    c0
    nfcv
    #
    va
    @16
    nfcv
    @26
    @13
    eqid
    @1
    @16
    @13
    cfv
    wceq
    c0
    eqidd
    frsucmpt
    mpan2
    @18
    @14
    @24
    c0
    @0
    @17
    @13
    fveq2
    eqeq1d
    syl5ibrcom
    rexlimiv
    jaoi
    syl
    syl5eq
    iuneq2i
    vi
    com
    iun0
    3eqtri
end
