include "cxr.mm"
include "wcel.mm"
include "crp.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "cxmu.mm"
include "co.mm"
include "xltmul1.mm"
include "wb.mm"
include "rpxr.mm"
include "wceq.mm"
include "xmulcom.mm"
include "3adant2.mm"
include "3adant1.mm"
include "breq12d.mm"
include "syl3an3.mm"
include "bitrd.mm"

theorem xltmul2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. RR+ ) -> ( A < B <-> ( C *e A ) < ( C *e B ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    crp
    wcel
    #
    w3a
    cA
    cB
    clt
    wbr
    cA
    cC
    cxmu
    co
    #
    cB
    cC
    cxmu
    co
    #
    clt
    wbr
    #
    cC
    cA
    cxmu
    co
    #
    cC
    cB
    cxmu
    co
    #
    clt
    wbr
    #
    cA
    cB
    cC
    xltmul1
    @2
    @0
    @1
    cC
    cxr
    wcel
    #
    @5
    @8
    wb
    cC
    rpxr
    @0
    @1
    @9
    w3a
    @3
    @6
    @4
    @7
    clt
    @0
    @9
    @3
    @6
    wceq
    @1
    cA
    cC
    xmulcom
    3adant2
    @1
    @9
    @4
    @7
    wceq
    @0
    cB
    cC
    xmulcom
    3adant1
    breq12d
    syl3an3
    bitrd
end
