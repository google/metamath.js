include "csdm.mm"
include "wbr.mm"
include "wa.mm"
include "sdomirr.mm"
include "sdomtr.mm"
include "mto.mm"

theorem sdomn2lp
  let cA: class A
  let cB: class B


  assert |- -. ( A ~< B /\ B ~< A )

  proof
    cA
    cB
    csdm
    wbr
    cB
    cA
    csdm
    wbr
    wa
    cA
    cA
    csdm
    wbr
    cA
    sdomirr
    cA
    cB
    cA
    sdomtr
    mto
end
