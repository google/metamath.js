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
include "3mix1d.mm"
include "wb.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "brcolinear.mm"
include "syl13anc.mm"
include "mpbird.mm"

theorem colineartriv1
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) -> A Colinear <. A , B >. )

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
    #
    ccolin
    wbr
    #
    cA
    @5
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
    cB
    cA
    cA
    cop
    cbtwn
    wbr
    #
    w3o
    #
    @4
    @7
    @8
    @9
    cA
    cB
    cN
    btwntriv1
    3mix1d
    @4
    @0
    @2
    @2
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
    #
    @11
    @0
    @2
    @3
    simp3
    cA
    cA
    cB
    cN
    brcolinear
    syl13anc
    mpbird
end
