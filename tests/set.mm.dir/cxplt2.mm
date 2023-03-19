include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "crp.mm"
include "w3a.mm"
include "wn.mm"
include "ccxp.mm"
include "co.mm"
include "clt.mm"
include "wb.mm"
include "cxple2.mm"
include "3com12.mm"
include "notbid.mm"
include "simp1l.mm"
include "simp2l.mm"
include "ltnled.mm"
include "simp1r.mm"
include "rpre.mm"
include "3ad2ant3.mm"
include "recxpcl.mm"
include "syl3anc.mm"
include "simp2r.mm"
include "3bitr4d.mm"

theorem cxplt2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 <_ B ) /\ C e. RR+ ) -> ( A < B <-> ( A ^c C ) < ( B ^c C ) ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
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
    cB
    cC
    ccxp
    co
    #
    cA
    cC
    ccxp
    co
    #
    cle
    wbr
    #
    wn
    cA
    cB
    clt
    wbr
    @10
    @9
    clt
    wbr
    @7
    @8
    @11
    @5
    @2
    @6
    @8
    @11
    wb
    cB
    cA
    cC
    cxple2
    3com12
    notbid
    @7
    cA
    cB
    @0
    @1
    @5
    @6
    simp1l
    #
    @2
    @3
    @4
    @6
    simp2l
    #
    ltnled
    @7
    @10
    @9
    @7
    @0
    @1
    cC
    cr
    wcel
    #
    @10
    cr
    wcel
    @12
    @0
    @1
    @5
    @6
    simp1r
    @6
    @2
    @14
    @5
    cC
    rpre
    3ad2ant3
    #
    cA
    cC
    recxpcl
    syl3anc
    @7
    @3
    @4
    @14
    @9
    cr
    wcel
    @13
    @2
    @3
    @4
    @6
    simp2r
    @15
    cB
    cC
    recxpcl
    syl3anc
    ltnled
    3bitr4d
end
