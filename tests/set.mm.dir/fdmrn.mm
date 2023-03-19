include "cdm.mm"
include "crn.mm"
include "wf.mm"
include "wfn.mm"
include "wfun.mm"
include "wss.mm"
include "ssid.mm"
include "df-f.mm"
include "mpbiran2.mm"
include "wceq.mm"
include "eqid.mm"
include "df-fn.mm"
include "bitr2i.mm"

theorem fdmrn
  let cF: class F


  assert |- ( Fun F <-> F : dom F --> ran F )

  proof
    cF
    cdm
    #
    cF
    crn
    #
    cF
    wf
    #
    cF
    @0
    wfn
    #
    cF
    wfun
    #
    @2
    @3
    @1
    @1
    wss
    @1
    ssid
    @0
    @1
    cF
    df-f
    mpbiran2
    @3
    @4
    @0
    @0
    wceq
    @0
    eqid
    cF
    @0
    df-fn
    mpbiran2
    bitr2i
end
