include "cflim.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "wss.mm"
include "ctop.mm"
include "cfil.mm"
include "crn.mm"
include "cuni.mm"
include "cpw.mm"
include "w3a.mm"
include "wa.mm"
include "elflim2.mm"
include "simprbi.mm"
include "simpld.mm"

theorem flimelbas
  let cA: class A
  let cF: class F
  let cJ: class J
  let cX: class X
  assume flimuni.1: |- X = U. J


  assert |- ( A e. ( J fLim F ) -> A e. X )

  proof
    cA
    cJ
    cF
    cflim
    co
    wcel
    #
    cA
    cX
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
    cX
    cpw
    wss
    w3a
    @1
    @2
    wa
    cA
    cF
    cJ
    cX
    flimuni.1
    elflim2
    simprbi
    simpld
end
