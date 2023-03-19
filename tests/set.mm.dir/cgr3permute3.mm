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
include "3simpa.mm"
include "cgrcomlr.mm"
include "syl3an.mm"
include "3simpb.mm"
include "3anbi12d.mm"
include "3anrot.mm"
include "syl6bbr.mm"
include "brcgr3.mm"
include "biid.mm"
include "syl3anb.mm"
include "3bitr4d.mm"

theorem cgr3permute3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) -> ( <. A , <. B , C >. >. Cgr3 <. D , <. E , F >. >. <-> <. B , <. C , A >. >. Cgr3 <. E , <. F , D >. >. ) )

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
    @15
    cB
    cA
    cop
    cE
    cD
    cop
    ccgr
    wbr
    #
    cC
    cA
    cop
    #
    cF
    cD
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
    cB
    @18
    cop
    cE
    @19
    cop
    ccgr3
    wbr
    #
    @10
    @16
    @17
    @20
    @15
    w3a
    @21
    @10
    @11
    @17
    @12
    @20
    @15
    @0
    @0
    @5
    @2
    @3
    wa
    @9
    @6
    @7
    wa
    @11
    @17
    wb
    @0
    id
    #
    @2
    @3
    @4
    3simpa
    @6
    @7
    @8
    3simpa
    cA
    cB
    cD
    cE
    cN
    cgrcomlr
    syl3an
    @0
    @0
    @5
    @2
    @4
    wa
    @9
    @6
    @8
    wa
    @12
    @20
    wb
    @23
    @2
    @3
    @4
    3simpb
    @6
    @7
    @8
    3simpb
    cA
    cC
    cD
    cF
    cN
    cgrcomlr
    syl3an
    3anbi12d
    @15
    @17
    @20
    3anrot
    syl6bbr
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
    @3
    @4
    @2
    w3a
    @9
    @7
    @8
    @6
    w3a
    @22
    @21
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
    brcgr3
    syl3anb
    3bitr4d
end
