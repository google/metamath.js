include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wo.mm"
include "coutsideof.mm"
include "wb.mm"
include "3ancoma.mm"
include "orcom.mm"
include "3anbi3i.mm"
include "bitri.mm"
include "a1i.mm"
include "broutsideof2.mm"
include "3ancomb.mm"
include "sylan2b.mm"
include "3bitr4d.mm"

theorem outsideofcom
  let cA: class A
  let cB: class B
  let cP: class P
  let cN: class N


  assert |- ( ( N e. NN /\ ( P e. ( EE ` N ) /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) ) -> ( P OutsideOf <. A , B >. <-> P OutsideOf <. B , A >. ) )

  proof
    cN
    cn
    wcel
    #
    cP
    cN
    cee
    cfv
    #
    wcel
    #
    cA
    @1
    wcel
    #
    cB
    @1
    wcel
    #
    w3a
    #
    wa
    #
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
    #
    cB
    cP
    cA
    cop
    cbtwn
    wbr
    #
    wo
    #
    w3a
    #
    @8
    @7
    @10
    @9
    wo
    #
    w3a
    #
    cP
    cA
    cB
    cop
    coutsideof
    wbr
    cP
    cB
    cA
    cop
    coutsideof
    wbr
    #
    @12
    @14
    wb
    @6
    @12
    @8
    @7
    @11
    w3a
    @14
    @7
    @8
    @11
    3ancoma
    @11
    @13
    @8
    @7
    @9
    @10
    orcom
    3anbi3i
    bitri
    a1i
    cA
    cB
    cP
    cN
    broutsideof2
    @5
    @0
    @2
    @4
    @3
    w3a
    @15
    @14
    wb
    @2
    @3
    @4
    3ancomb
    cB
    cA
    cP
    cN
    broutsideof2
    sylan2b
    3bitr4d
end
