include "cflim.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "flimneiss.mm"
include "sselda.mm"

theorem flimnei
  let cA: class A
  let cF: class F
  let cJ: class J
  let cN: class N


  assert |- ( ( A e. ( J fLim F ) /\ N e. ( ( nei ` J ) ` { A } ) ) -> N e. F )

  proof
    cA
    cJ
    cF
    cflim
    co
    wcel
    cA
    csn
    cJ
    cnei
    cfv
    cfv
    cF
    cN
    cA
    cF
    cJ
    flimneiss
    sselda
end
