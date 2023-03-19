include "cvv.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "wb.mm"
include "elmapg.mm"
include "mp2an.mm"

theorem elmap
  let cA: class A
  let cB: class B
  let cF: class F
  let vg: setvar g
  let vf: setvar f
  assume elmap.1: |- A e. _V
  assume elmap.2: |- B e. _V


  assert |- ( F e. ( A ^m B ) <-> F : B --> A )

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
    cmap
    co
    wcel
    cB
    cA
    cF
    wf
    wb
    elmap.1
    elmap.2
    cA
    cB
    cF
    cvv
    cvv
    elmapg
    mp2an
end
