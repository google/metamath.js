include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "ccgr3.mm"
include "wbr.mm"
include "cgr3permute3.mm"
include "wb.mm"
include "biid.mm"
include "3anrot.mm"
include "syl3anb.mm"
include "bitrd.mm"

theorem cgr3permute4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) -> ( <. A , <. B , C >. >. Cgr3 <. D , <. E , F >. >. <-> <. C , <. A , B >. >. Cgr3 <. F , <. D , E >. >. ) )

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
    cD
    @1
    wcel
    #
    cE
    @1
    wcel
    #
    cF
    @1
    wcel
    #
    w3a
    #
    w3a
    cA
    cB
    cC
    cop
    cop
    cD
    cE
    cF
    cop
    cop
    ccgr3
    wbr
    cB
    cC
    cA
    cop
    cop
    cE
    cF
    cD
    cop
    cop
    ccgr3
    wbr
    #
    cC
    cA
    cB
    cop
    cop
    cF
    cD
    cE
    cop
    cop
    ccgr3
    wbr
    #
    cA
    cB
    cC
    cD
    cE
    cF
    cN
    cgr3permute3
    @0
    @0
    @5
    @3
    @4
    @2
    w3a
    @9
    @7
    @8
    @6
    w3a
    @10
    @11
    wb
    @0
    biid
    @2
    @3
    @4
    3anrot
    @6
    @7
    @8
    3anrot
    cB
    cC
    cA
    cE
    cF
    cD
    cN
    cgr3permute3
    syl3anb
    bitrd
end
