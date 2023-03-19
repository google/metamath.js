include "cvv.mm"
include "wcel.mm"
include "cpm.mm"
include "co.mm"
include "wfun.mm"
include "cxp.mm"
include "wss.mm"
include "wa.mm"
include "wb.mm"
include "elpmg.mm"
include "mp2an.mm"

theorem elpm
  let cA: class A
  let cB: class B
  let cF: class F
  let vg: setvar g
  let vf: setvar f
  assume elmap.1: |- A e. _V
  assume elmap.2: |- B e. _V


  assert |- ( F e. ( A ^pm B ) <-> ( Fun F /\ F C_ ( B X. A ) ) )

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
    wfun
    cF
    cB
    cA
    cxp
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
    elpmg
    mp2an
end
