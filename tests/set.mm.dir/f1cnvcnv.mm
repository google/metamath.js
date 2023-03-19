include "cdm.mm"
include "cvv.mm"
include "ccnv.mm"
include "wf1.mm"
include "wf.mm"
include "wfun.mm"
include "wa.mm"
include "df-f1.mm"
include "wfn.mm"
include "dffn2.mm"
include "wceq.mm"
include "dmcnvcnv.mm"
include "df-fn.mm"
include "mpbiran2.mm"
include "bitr3i.mm"
include "wrel.mm"
include "relcnv.mm"
include "dfrel2.mm"
include "mpbi.mm"
include "funeqi.mm"
include "anbi12ci.mm"
include "bitri.mm"

theorem f1cnvcnv
  let cA: class A


  assert |- ( `' `' A : dom A -1-1-> _V <-> ( Fun `' A /\ Fun `' `' A ) )

  proof
    cA
    cdm
    #
    cvv
    cA
    ccnv
    #
    ccnv
    #
    wf1
    @0
    cvv
    @2
    wf
    #
    @2
    ccnv
    #
    wfun
    #
    wa
    @1
    wfun
    #
    @2
    wfun
    #
    wa
    @0
    cvv
    @2
    df-f1
    @3
    @7
    @5
    @6
    @3
    @2
    @0
    wfn
    #
    @7
    @0
    @2
    dffn2
    @8
    @7
    @2
    cdm
    @0
    wceq
    cA
    dmcnvcnv
    @2
    @0
    df-fn
    mpbiran2
    bitr3i
    @4
    @1
    @1
    wrel
    @4
    @1
    wceq
    cA
    relcnv
    @1
    dfrel2
    mpbi
    funeqi
    anbi12ci
    bitri
end
