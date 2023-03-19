include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "clog.mm"
include "cfv.mm"
include "crn.mm"
include "logrncl.mm"
include "logrncn.mm"
include "syl.mm"

theorem logcl
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( log ` A ) e. CC )

  proof
    cA
    cc
    wcel
    cA
    cc0
    wne
    wa
    cA
    clog
    cfv
    #
    clog
    crn
    wcel
    @0
    cc
    wcel
    cA
    logrncl
    @0
    logrncn
    syl
end
