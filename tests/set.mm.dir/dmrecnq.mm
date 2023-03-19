include "crq.mm"
include "cdm.mm"
include "cnq.mm"
include "cxp.mm"
include "wss.mm"
include "cmq.mm"
include "ccnv.mm"
include "c1q.mm"
include "csn.mm"
include "cima.mm"
include "df-rq.mm"
include "cnvimass.mm"
include "eqsstri.mm"
include "mulnqf.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "dmss.mm"
include "ax-mp.mm"
include "dmxpid.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wbr.mm"
include "cop.mm"
include "wceq.mm"
include "recclnq.mm"
include "opelxpi.mm"
include "mpdan.mm"
include "co.mm"
include "df-ov.mm"
include "recidnq.mm"
include "syl5eqr.mm"
include "wf.mm"
include "wfn.mm"
include "wa.mm"
include "wb.mm"
include "ffn.mm"
include "fniniseg.mm"
include "mp2b.mm"
include "sylanbrc.mm"
include "syl6eleqr.mm"
include "df-br.mm"
include "sylibr.mm"
include "vex.mm"
include "fvex.mm"
include "breldm.mm"
include "syl.mm"
include "ssriv.mm"
include "eqssi.mm"

theorem dmrecnq
  let vx: setvar x


  assert |- dom *Q = Q.

  proof
    crq
    cdm
    #
    cnq
    @0
    cnq
    cnq
    cxp
    #
    cdm
    #
    cnq
    crq
    @1
    wss
    @0
    @2
    wss
    crq
    cmq
    cdm
    #
    @1
    crq
    cmq
    ccnv
    c1q
    csn
    #
    cima
    #
    @3
    df-rq
    cmq
    @4
    cnvimass
    eqsstri
    @1
    cnq
    cmq
    mulnqf
    fdmi
    sseqtri
    crq
    @1
    dmss
    ax-mp
    cnq
    dmxpid
    sseqtri
    vx
    cnq
    @0
    vx
    cv
    #
    cnq
    wcel
    #
    @6
    @6
    crq
    cfv
    #
    crq
    wbr
    #
    @6
    @0
    wcel
    @7
    @6
    @8
    cop
    #
    crq
    wcel
    @9
    @7
    @10
    @5
    crq
    @7
    @10
    @1
    wcel
    #
    @10
    cmq
    cfv
    #
    c1q
    wceq
    #
    @10
    @5
    wcel
    #
    @7
    @8
    cnq
    wcel
    @11
    @6
    recclnq
    @6
    @8
    cnq
    cnq
    opelxpi
    mpdan
    @7
    @12
    @6
    @8
    cmq
    co
    c1q
    @6
    @8
    cmq
    df-ov
    @6
    recidnq
    syl5eqr
    @1
    cnq
    cmq
    wf
    cmq
    @1
    wfn
    @14
    @11
    @13
    wa
    wb
    mulnqf
    @1
    cnq
    cmq
    ffn
    @1
    c1q
    @10
    cmq
    fniniseg
    mp2b
    sylanbrc
    df-rq
    syl6eleqr
    @6
    @8
    crq
    df-br
    sylibr
    @6
    @8
    crq
    vx
    vex
    @6
    crq
    fvex
    breldm
    syl
    ssriv
    eqssi
end
