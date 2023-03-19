include "cflim.mm"
include "co.mm"
include "wcel.mm"
include "ctop.mm"
include "cfil.mm"
include "crn.mm"
include "cuni.mm"
include "cpw.mm"
include "wss.mm"
include "w3a.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "wa.mm"
include "eqid.mm"
include "elflim2.mm"
include "simplbi.mm"
include "simp1d.mm"

theorem flimtop
  let cA: class A
  let cF: class F
  let cJ: class J


  assert |- ( A e. ( J fLim F ) -> J e. Top )

  proof
    cA
    cJ
    cF
    cflim
    co
    wcel
    #
    cJ
    ctop
    wcel
    #
    cF
    cfil
    crn
    cuni
    wcel
    #
    cF
    cJ
    cuni
    #
    cpw
    wss
    #
    @0
    @1
    @2
    @4
    w3a
    cA
    @3
    wcel
    cA
    csn
    cJ
    cnei
    cfv
    cfv
    cF
    wss
    wa
    cA
    cF
    cJ
    @3
    @3
    eqid
    elflim2
    simplbi
    simp1d
end
