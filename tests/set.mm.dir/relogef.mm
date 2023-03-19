include "cr.mm"
include "wcel.mm"
include "clog.mm"
include "crn.mm"
include "ce.mm"
include "cfv.mm"
include "wceq.mm"
include "relogrn.mm"
include "logef.mm"
include "syl.mm"

theorem relogef
  let cA: class A


  assert |- ( A e. RR -> ( log ` ( exp ` A ) ) = A )

  proof
    cA
    cr
    wcel
    cA
    clog
    crn
    wcel
    cA
    ce
    cfv
    clog
    cfv
    cA
    wceq
    cA
    relogrn
    cA
    logef
    syl
end
