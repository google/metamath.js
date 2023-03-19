include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "ccm.mm"
include "wbr.mm"
include "ssinss1.mm"
include "cmbr4i.mm"
include "sylibr.mm"

theorem lecmi
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH


  assert |- ( A C_ B -> A C_H B )

  proof
    cA
    cB
    wss
    cA
    cA
    cort
    cfv
    cB
    chj
    co
    #
    cin
    cB
    wss
    cA
    cB
    ccm
    wbr
    cA
    @0
    cB
    ssinss1
    cA
    cB
    pjoml2.1
    pjoml2.2
    cmbr4i
    sylibr
end
