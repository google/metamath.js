include "cxr.mm"
include "wcel.mm"
include "crp.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "cxmu.mm"
include "co.mm"
include "clt.mm"
include "wb.mm"
include "xlemul1.mm"
include "3com12.mm"
include "notbid.mm"
include "xrltnle.mm"
include "3adant3.mm"
include "simp1.mm"
include "rpxr.mm"
include "3ad2ant3.mm"
include "xmulcl.mm"
include "syl2anc.mm"
include "simp2.mm"
include "3bitr4d.mm"

theorem xltmul1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. RR+ ) -> ( A < B <-> ( A *e C ) < ( B *e C ) ) )

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
    #
    cB
    cA
    cle
    wbr
    #
    wn
    #
    cB
    cC
    cxmu
    co
    #
    cA
    cC
    cxmu
    co
    #
    cle
    wbr
    #
    wn
    #
    cA
    cB
    clt
    wbr
    #
    @7
    @6
    clt
    wbr
    #
    @3
    @4
    @8
    @1
    @0
    @2
    @4
    @8
    wb
    cB
    cA
    cC
    xlemul1
    3com12
    notbid
    @0
    @1
    @10
    @5
    wb
    @2
    cA
    cB
    xrltnle
    3adant3
    @3
    @7
    cxr
    wcel
    #
    @6
    cxr
    wcel
    #
    @11
    @9
    wb
    @3
    @0
    cC
    cxr
    wcel
    #
    @12
    @0
    @1
    @2
    simp1
    @2
    @0
    @14
    @1
    cC
    rpxr
    3ad2ant3
    #
    cA
    cC
    xmulcl
    syl2anc
    @3
    @1
    @14
    @13
    @0
    @1
    @2
    simp2
    @15
    cB
    cC
    xmulcl
    syl2anc
    @7
    @6
    xrltnle
    syl2anc
    3bitr4d
end
