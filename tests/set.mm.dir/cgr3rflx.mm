include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "ccgr3.mm"
include "wbr.mm"
include "ccgr.mm"
include "cgrrflx.mm"
include "3adant3r3.mm"
include "3adant3r2.mm"
include "3adant3r1.mm"
include "wb.mm"
include "brcgr3.mm"
include "3anidm23.mm"
include "mpbir3and.mm"

theorem cgr3rflx
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) -> <. A , <. B , C >. >. Cgr3 <. A , <. B , C >. >. )

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
    cA
    cB
    cC
    cop
    #
    cop
    #
    @7
    ccgr3
    wbr
    #
    cA
    cB
    cop
    #
    @9
    ccgr
    wbr
    #
    cA
    cC
    cop
    #
    @11
    ccgr
    wbr
    #
    @6
    @6
    ccgr
    wbr
    #
    @0
    @2
    @3
    @10
    @4
    cA
    cB
    cN
    cgrrflx
    3adant3r3
    @0
    @2
    @4
    @12
    @3
    cA
    cC
    cN
    cgrrflx
    3adant3r2
    @0
    @3
    @4
    @13
    @2
    cB
    cC
    cN
    cgrrflx
    3adant3r1
    @0
    @5
    @8
    @10
    @12
    @13
    w3a
    wb
    cA
    cB
    cC
    cA
    cB
    cC
    cN
    brcgr3
    3anidm23
    mpbir3and
end
