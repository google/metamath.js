include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "ccgr3.mm"
include "wa.mm"
include "wb.mm"
include "id.mm"
include "3simpc.mm"
include "cgrcomlr.mm"
include "syl3an.mm"
include "3anbi3d.mm"
include "3ancoma.mm"
include "syl6bb.mm"
include "brcgr3.mm"
include "biid.mm"
include "3ancomb.mm"
include "syl3anb.mm"
include "3bitr4d.mm"

theorem cgr3permute1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) -> ( <. A , <. B , C >. >. Cgr3 <. D , <. E , F >. >. <-> <. A , <. C , B >. >. Cgr3 <. D , <. F , E >. >. ) )

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
    #
    cA
    cB
    cop
    cD
    cE
    cop
    ccgr
    wbr
    #
    cA
    cC
    cop
    cD
    cF
    cop
    ccgr
    wbr
    #
    cB
    cC
    cop
    #
    cE
    cF
    cop
    #
    ccgr
    wbr
    #
    w3a
    #
    @12
    @11
    cC
    cB
    cop
    #
    cF
    cE
    cop
    #
    ccgr
    wbr
    #
    w3a
    #
    cA
    @13
    cop
    cD
    @14
    cop
    ccgr3
    wbr
    cA
    @17
    cop
    cD
    @18
    cop
    ccgr3
    wbr
    #
    @10
    @16
    @11
    @12
    @19
    w3a
    @20
    @10
    @15
    @19
    @11
    @12
    @0
    @0
    @5
    @3
    @4
    wa
    @9
    @7
    @8
    wa
    @15
    @19
    wb
    @0
    id
    @2
    @3
    @4
    3simpc
    @6
    @7
    @8
    3simpc
    cB
    cC
    cE
    cF
    cN
    cgrcomlr
    syl3an
    3anbi3d
    @11
    @12
    @19
    3ancoma
    syl6bb
    cA
    cB
    cC
    cD
    cE
    cF
    cN
    brcgr3
    @0
    @0
    @5
    @2
    @4
    @3
    w3a
    @9
    @6
    @8
    @7
    w3a
    @21
    @20
    wb
    @0
    biid
    @2
    @3
    @4
    3ancomb
    @6
    @7
    @8
    3ancomb
    cA
    cC
    cB
    cD
    cF
    cE
    cN
    brcgr3
    syl3anb
    3bitr4d
end
