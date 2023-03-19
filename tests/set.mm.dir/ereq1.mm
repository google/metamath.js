include "wceq.mm"
include "wrel.mm"
include "cdm.mm"
include "ccnv.mm"
include "ccom.mm"
include "cun.mm"
include "wss.mm"
include "w3a.mm"
include "wer.mm"
include "releq.mm"
include "dmeq.mm"
include "eqeq1d.mm"
include "cnveq.mm"
include "coeq1.mm"
include "coeq2.mm"
include "eqtrd.mm"
include "uneq12d.mm"
include "sseq1d.mm"
include "sseq2.mm"
include "bitrd.mm"
include "3anbi123d.mm"
include "df-er.mm"
include "3bitr4g.mm"

theorem ereq1
  let cA: class A
  let cR: class R
  let cS: class S


  assert |- ( R = S -> ( R Er A <-> S Er A ) )

  proof
    cR
    cS
    wceq
    #
    cR
    wrel
    #
    cR
    cdm
    #
    cA
    wceq
    #
    cR
    ccnv
    #
    cR
    cR
    ccom
    #
    cun
    #
    cR
    wss
    #
    w3a
    cS
    wrel
    #
    cS
    cdm
    #
    cA
    wceq
    #
    cS
    ccnv
    #
    cS
    cS
    ccom
    #
    cun
    #
    cS
    wss
    #
    w3a
    cA
    cR
    wer
    cA
    cS
    wer
    @0
    @1
    @8
    @3
    @10
    @7
    @14
    cR
    cS
    releq
    @0
    @2
    @9
    cA
    cR
    cS
    dmeq
    eqeq1d
    @0
    @7
    @13
    cR
    wss
    @14
    @0
    @6
    @13
    cR
    @0
    @4
    @11
    @5
    @12
    cR
    cS
    cnveq
    @0
    @5
    cS
    cR
    ccom
    @12
    cR
    cS
    cR
    coeq1
    cR
    cS
    cS
    coeq2
    eqtrd
    uneq12d
    sseq1d
    cR
    cS
    @13
    sseq2
    bitrd
    3anbi123d
    cA
    cR
    df-er
    cA
    cS
    df-er
    3bitr4g
end
