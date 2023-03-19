include "cvv.mm"
include "wcel.mm"
include "cpm.mm"
include "co.mm"
include "cdm.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "wb.mm"
include "elpm2g.mm"
include "mp2an.mm"

theorem elpm2
  let cA: class A
  let cB: class B
  let cF: class F
  let vg: setvar g
  let vf: setvar f
  assume elmap.1: |- A e. _V
  assume elmap.2: |- B e. _V


  assert |- ( F e. ( A ^pm B ) <-> ( F : dom F --> A /\ dom F C_ B ) )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cF
    cA
    cB
    cpm
    co
    wcel
    cF
    cdm
    #
    cA
    cF
    wf
    @0
    cB
    wss
    wa
    wb
    elmap.1
    elmap.2
    cA
    cB
    cF
    cvv
    cvv
    elpm2g
    mp2an
end
