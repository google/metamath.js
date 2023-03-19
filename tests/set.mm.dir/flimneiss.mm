include "cflim.mm"
include "co.mm"
include "wcel.mm"
include "cuni.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "wss.mm"
include "ctop.mm"
include "cfil.mm"
include "crn.mm"
include "cpw.mm"
include "w3a.mm"
include "wa.mm"
include "eqid.mm"
include "elflim2.mm"
include "simprbi.mm"
include "simprd.mm"

theorem flimneiss
  let cA: class A
  let cF: class F
  let cJ: class J


  assert |- ( A e. ( J fLim F ) -> ( ( nei ` J ) ` { A } ) C_ F )

  proof
    cA
    cJ
    cF
    cflim
    co
    wcel
    #
    cA
    cJ
    cuni
    #
    wcel
    #
    cA
    csn
    cJ
    cnei
    cfv
    cfv
    cF
    wss
    #
    @0
    cJ
    ctop
    wcel
    cF
    cfil
    crn
    cuni
    wcel
    cF
    @1
    cpw
    wss
    w3a
    @2
    @3
    wa
    cA
    cF
    cJ
    @1
    @1
    eqid
    elflim2
    simprbi
    simprd
end
