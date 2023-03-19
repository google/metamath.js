include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "clog.mm"
include "cfv.mm"
include "crn.mm"
include "eldifsn.mm"
include "wf1o.mm"
include "wf.mm"
include "logf1o.mm"
include "f1of.mm"
include "ax-mp.mm"
include "ffvelrni.mm"
include "sylbir.mm"

theorem logrncl
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( log ` A ) e. ran log )

  proof
    cA
    cc
    wcel
    cA
    cc0
    wne
    wa
    cA
    cc
    cc0
    csn
    cdif
    #
    wcel
    cA
    clog
    cfv
    clog
    crn
    #
    wcel
    cA
    cc
    cc0
    eldifsn
    @0
    @1
    cA
    clog
    @0
    @1
    clog
    wf1o
    @0
    @1
    clog
    wf
    logf1o
    @0
    @1
    clog
    f1of
    ax-mp
    ffvelrni
    sylbir
end
