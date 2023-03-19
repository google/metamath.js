include "cxp.mm"
include "wer.mm"
include "wrel.mm"
include "cdm.mm"
include "wceq.mm"
include "ccnv.mm"
include "ccom.mm"
include "cun.mm"
include "wss.mm"
include "relxp.mm"
include "dmxpid.mm"
include "cnvxp.mm"
include "xpidtr.mm"
include "uneq1.mm"
include "unss2.mm"
include "wi.mm"
include "unidm.mm"
include "wa.mm"
include "eqtr.mm"
include "sseq2.mm"
include "biimpd.mm"
include "syl.mm"
include "mpan2.mm"
include "syl2im.mm"
include "mp2.mm"
include "df-er.mm"
include "mpbir3an.mm"

theorem xpider
  let cA: class A


  assert |- ( A X. A ) Er A

  proof
    cA
    cA
    cA
    cxp
    #
    wer
    @0
    wrel
    @0
    cdm
    cA
    wceq
    @0
    ccnv
    #
    @0
    @0
    ccom
    #
    cun
    #
    @0
    wss
    #
    cA
    cA
    relxp
    cA
    dmxpid
    @1
    @0
    wceq
    #
    @2
    @0
    wss
    #
    @4
    cA
    cA
    cnvxp
    cA
    xpidtr
    @5
    @1
    @0
    cun
    #
    @0
    @0
    cun
    #
    wceq
    #
    @6
    @3
    @7
    wss
    #
    @4
    @1
    @0
    @0
    uneq1
    @2
    @0
    @1
    unss2
    @9
    @8
    @0
    wceq
    #
    @10
    @4
    wi
    #
    @0
    unidm
    @9
    @11
    wa
    @7
    @0
    wceq
    #
    @12
    @7
    @8
    @0
    eqtr
    @13
    @10
    @4
    @7
    @0
    @3
    sseq2
    biimpd
    syl
    mpan2
    syl2im
    mp2
    cA
    @0
    df-er
    mpbir3an
end
