include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "coutsideof.mm"
include "wbr.mm"
include "wne.mm"
include "cbtwn.mm"
include "wo.mm"
include "broutsideof2.mm"
include "simp2.mm"
include "syl6bi.mm"

theorem outsidene2
  let cA: class A
  let cB: class B
  let cP: class P
  let cN: class N


  assert |- ( ( N e. NN /\ ( P e. ( EE ` N ) /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) ) -> ( P OutsideOf <. A , B >. -> B =/= P ) )

  proof
    cN
    cn
    wcel
    cP
    cN
    cee
    cfv
    #
    wcel
    cA
    @0
    wcel
    cB
    @0
    wcel
    w3a
    wa
    cP
    cA
    cB
    cop
    coutsideof
    wbr
    cA
    cP
    wne
    #
    cB
    cP
    wne
    #
    cA
    cP
    cB
    cop
    cbtwn
    wbr
    cB
    cP
    cA
    cop
    cbtwn
    wbr
    wo
    #
    w3a
    @2
    cA
    cB
    cP
    cN
    broutsideof2
    @1
    @2
    @3
    simp2
    syl6bi
end
