include "cfsupp.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "relfsupp.mm"
include "brrelexi.mm"
include "con3i.mm"

theorem relprcnfsupp
  let cA: class A
  let cZ: class Z


  assert |- ( -. A e. _V -> -. A finSupp Z )

  proof
    cA
    cZ
    cfsupp
    wbr
    cA
    cvv
    wcel
    cA
    cZ
    cfsupp
    relfsupp
    brrelexi
    con3i
end
