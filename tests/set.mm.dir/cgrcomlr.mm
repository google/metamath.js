include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "cgrcoml.mm"
include "wb.mm"
include "ancom.mm"
include "cgrcomr.mm"
include "syl3an2b.mm"
include "bitrd.mm"

theorem cgrcomlr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( <. A , B >. Cgr <. C , D >. <-> <. B , A >. Cgr <. D , C >. ) )

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
    wa
    #
    cC
    @1
    wcel
    cD
    @1
    wcel
    wa
    #
    w3a
    cA
    cB
    cop
    cC
    cD
    cop
    #
    ccgr
    wbr
    cB
    cA
    cop
    #
    @6
    ccgr
    wbr
    #
    @7
    cD
    cC
    cop
    ccgr
    wbr
    #
    cA
    cB
    cC
    cD
    cN
    cgrcoml
    @4
    @0
    @3
    @2
    wa
    @5
    @8
    @9
    wb
    @2
    @3
    ancom
    cB
    cA
    cC
    cD
    cN
    cgrcomr
    syl3an2b
    bitrd
end
