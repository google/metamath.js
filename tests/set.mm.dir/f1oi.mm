include "cid.mm"
include "cres.mm"
include "wf1o.mm"
include "wfn.mm"
include "ccnv.mm"
include "fnresi.mm"
include "cnvresid.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "dff1o4.mm"
include "mpbir2an.mm"

theorem f1oi
  let cA: class A


  assert |- ( _I |` A ) : A -1-1-onto-> A

  proof
    cA
    cA
    cid
    cA
    cres
    #
    wf1o
    @0
    cA
    wfn
    #
    @0
    ccnv
    #
    cA
    wfn
    #
    cA
    fnresi
    #
    @3
    @1
    @4
    cA
    @2
    @0
    cA
    cnvresid
    fneq1i
    mpbir
    cA
    cA
    @0
    dff1o4
    mpbir2an
end
