include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cop.mm"
include "c0.mm"
include "wceq.mm"
include "simpl.mm"
include "con3i.mm"
include "opprc.mm"
include "syl.mm"

theorem opprc1
  let cA: class A
  let cB: class B


  assert |- ( -. A e. _V -> <. A , B >. = (/) )

  proof
    cA
    cvv
    wcel
    #
    wn
    @0
    cB
    cvv
    wcel
    #
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
    @0
    @1
    simpl
    con3i
    cA
    cB
    opprc
    syl
end
