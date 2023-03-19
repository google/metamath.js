include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "ccolin.mm"
include "wbr.mm"
include "cbtwn.mm"
include "w3o.mm"
include "btwntriv1.mm"
include "3mix2d.mm"
include "3com23.mm"
include "wb.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "brcolinear.mm"
include "syl13anc.mm"
include "mpbird.mm"

theorem colineartriv2
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) -> A Colinear <. B , B >. )

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
    cB
    cB
    cop
    #
    ccolin
    wbr
    #
    cA
    @5
    cbtwn
    wbr
    #
    cB
    cB
    cA
    cop
    cbtwn
    wbr
    #
    cB
    cA
    cB
    cop
    cbtwn
    wbr
    #
    w3o
    #
    @0
    @3
    @2
    @10
    @0
    @3
    @2
    w3a
    @8
    @7
    @9
    cB
    cA
    cN
    btwntriv1
    3mix2d
    3com23
    @4
    @0
    @2
    @3
    @3
    @6
    @10
    wb
    @0
    @2
    @3
    simp1
    @0
    @2
    @3
    simp2
    @0
    @2
    @3
    simp3
    #
    @11
    cA
    cB
    cB
    cN
    brcolinear
    syl13anc
    mpbird
end
