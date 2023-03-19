include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "btwntriv2.mm"
include "3com23.mm"
include "wb.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "btwncom.mm"
include "syl13anc.mm"
include "mpbird.mm"

theorem btwntriv1
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) -> A Btwn <. A , B >. )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    w3a
    #
    cA
    cA
    cB
    cop
    cbtwn
    wbr
    #
    cA
    cB
    cA
    cop
    cbtwn
    wbr
    #
    @0
    @3
    @2
    @6
    cB
    cA
    cN
    btwntriv2
    3com23
    @4
    @0
    @2
    @2
    @3
    @5
    @6
    wb
    @0
    @2
    @3
    simp1
    @0
    @2
    @3
    simp2
    #
    @7
    @0
    @2
    @3
    simp3
    cA
    cA
    cB
    cN
    btwncom
    syl13anc
    mpbird
end
