include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "w3o.mm"
include "ccolin.mm"
include "btwncom.mm"
include "wb.mm"
include "3anrot.mm"
include "sylan2b.mm"
include "sylan2br.mm"
include "3orbi123d.mm"
include "3orcomb.mm"
include "syl6bb.mm"
include "brcolinear.mm"
include "3ancomb.mm"
include "3bitr4d.mm"

theorem colinearperm1
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) -> ( A Colinear <. B , C >. <-> A Colinear <. C , B >. ) )

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
    cC
    @1
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cB
    cC
    cop
    #
    cbtwn
    wbr
    #
    cB
    cC
    cA
    cop
    cbtwn
    wbr
    #
    cC
    cA
    cB
    cop
    cbtwn
    wbr
    #
    w3o
    #
    cA
    cC
    cB
    cop
    #
    cbtwn
    wbr
    #
    cC
    cB
    cA
    cop
    cbtwn
    wbr
    #
    cB
    cA
    cC
    cop
    cbtwn
    wbr
    #
    w3o
    #
    cA
    @7
    ccolin
    wbr
    cA
    @12
    ccolin
    wbr
    #
    @6
    @11
    @13
    @15
    @14
    w3o
    @16
    @6
    @8
    @13
    @9
    @15
    @10
    @14
    cA
    cB
    cC
    cN
    btwncom
    @5
    @0
    @3
    @4
    @2
    w3a
    @9
    @15
    wb
    @2
    @3
    @4
    3anrot
    cB
    cC
    cA
    cN
    btwncom
    sylan2b
    @5
    @0
    @4
    @2
    @3
    w3a
    @10
    @14
    wb
    @4
    @2
    @3
    3anrot
    cC
    cA
    cB
    cN
    btwncom
    sylan2br
    3orbi123d
    @13
    @15
    @14
    3orcomb
    syl6bb
    cA
    cB
    cC
    cN
    brcolinear
    @5
    @0
    @2
    @4
    @3
    w3a
    @17
    @16
    wb
    @2
    @3
    @4
    3ancomb
    cA
    cC
    cB
    cN
    brcolinear
    sylan2b
    3bitr4d
end
