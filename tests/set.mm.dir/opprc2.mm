include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cop.mm"
include "c0.mm"
include "wceq.mm"
include "simpr.mm"
include "con3i.mm"
include "opprc.mm"
include "syl.mm"

theorem opprc2
  let cA: class A
  let cB: class B


  assert |- ( -. B e. _V -> <. A , B >. = (/) )

  proof
    cB
    cvv
    wcel
    #
    wn
    cA
    cvv
    wcel
    #
    @0
    wa
    #
    wn
    cA
    cB
    cop
    c0
    wceq
    @2
    @0
    @1
    @0
    simpr
    con3i
    cA
    cB
    opprc
    syl
end
