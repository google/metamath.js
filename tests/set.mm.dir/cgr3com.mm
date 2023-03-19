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
include "cgrcom.mm"
include "syl3an.mm"
include "3simpb.mm"
include "3simpc.mm"
include "3anbi123d.mm"
include "brcgr3.mm"
include "3com23.mm"
include "3bitr4d.mm"

theorem cgr3com
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) -> ( <. A , <. B , C >. >. Cgr3 <. D , <. E , F >. >. <-> <. D , <. E , F >. >. Cgr3 <. A , <. B , C >. >. ) )

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
    #
    cD
    cE
    cop
    #
    ccgr
    wbr
    #
    cA
    cC
    cop
    #
    cD
    cF
    cop
    #
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
    @12
    @11
    ccgr
    wbr
    #
    @15
    @14
    ccgr
    wbr
    #
    @18
    @17
    ccgr
    wbr
    #
    w3a
    #
    cA
    @17
    cop
    #
    cD
    @18
    cop
    #
    ccgr3
    wbr
    @25
    @24
    ccgr3
    wbr
    #
    @10
    @13
    @20
    @16
    @21
    @19
    @22
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
    @13
    @20
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
    cgrcom
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
    @16
    @21
    wb
    @27
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
    cgrcom
    syl3an
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
    @19
    @22
    wb
    @27
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
    cgrcom
    syl3an
    3anbi123d
    cA
    cB
    cC
    cD
    cE
    cF
    cN
    brcgr3
    @0
    @9
    @5
    @26
    @23
    wb
    cD
    cE
    cF
    cA
    cB
    cC
    cN
    brcgr3
    3com23
    3bitr4d
end
