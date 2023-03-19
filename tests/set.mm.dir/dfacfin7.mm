include "cvv.mm"
include "ccrd.mm"
include "cdm.mm"
include "cdif.mm"
include "cfn.mm"
include "wss.mm"
include "cun.mm"
include "wceq.mm"
include "wac.mm"
include "cfin7.mm"
include "ssequn2.mm"
include "dfac10.mm"
include "cv.mm"
include "finnum.mm"
include "ssriv.mm"
include "mpbi.mm"
include "eqeq1i.mm"
include "bitr4i.mm"
include "ssv.mm"
include "eqss.mm"
include "mpbiran.mm"
include "ssundif.mm"
include "3bitri.mm"
include "dffin7-2.mm"
include "3bitr4i.mm"

theorem dfacfin7
  let vx: setvar x


  assert |- ( CHOICE <-> Fin7 = Fin )

  proof
    cvv
    ccrd
    cdm
    #
    cdif
    #
    cfn
    wss
    #
    cfn
    @1
    cun
    #
    cfn
    wceq
    wac
    cfin7
    cfn
    wceq
    @1
    cfn
    ssequn2
    wac
    @0
    cfn
    cun
    #
    cvv
    wceq
    #
    cvv
    @4
    wss
    #
    @2
    wac
    @0
    cvv
    wceq
    @5
    dfac10
    @4
    @0
    cvv
    cfn
    @0
    wss
    @4
    @0
    wceq
    vx
    cfn
    @0
    vx
    cv
    finnum
    ssriv
    cfn
    @0
    ssequn2
    mpbi
    eqeq1i
    bitr4i
    @5
    @4
    cvv
    wss
    @6
    @4
    ssv
    @4
    cvv
    eqss
    mpbiran
    cvv
    @0
    cfn
    ssundif
    3bitri
    cfin7
    @3
    cfn
    dffin7-2
    eqeq1i
    3bitr4i
end
