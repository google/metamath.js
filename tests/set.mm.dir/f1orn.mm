include "crn.mm"
include "wf1o.mm"
include "wfn.mm"
include "ccnv.mm"
include "wfun.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "dff1o2.mm"
include "eqid.mm"
include "df-3an.mm"
include "mpbiran2.mm"
include "bitri.mm"

theorem f1orn
  let cA: class A
  let cF: class F


  assert |- ( F : A -1-1-onto-> ran F <-> ( F Fn A /\ Fun `' F ) )

  proof
    cA
    cF
    crn
    #
    cF
    wf1o
    cF
    cA
    wfn
    #
    cF
    ccnv
    wfun
    #
    @0
    @0
    wceq
    #
    w3a
    #
    @1
    @2
    wa
    #
    cA
    @0
    cF
    dff1o2
    @4
    @5
    @3
    @0
    eqid
    @1
    @2
    @3
    df-3an
    mpbiran2
    bitri
end
