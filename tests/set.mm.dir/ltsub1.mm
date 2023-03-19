include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wb.mm"
include "lesub1.mm"
include "3com12.mm"
include "notbid.mm"
include "simp1.mm"
include "simp2.mm"
include "ltnled.mm"
include "simp3.mm"
include "resubcld.mm"
include "3bitr4d.mm"

theorem ltsub1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A < B <-> ( A - C ) < ( B - C ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cr
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
    cmin
    co
    #
    cA
    cC
    cmin
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
    @6
    @5
    clt
    wbr
    @3
    @4
    @7
    @1
    @0
    @2
    @4
    @7
    wb
    cB
    cA
    cC
    lesub1
    3com12
    notbid
    @3
    cA
    cB
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    #
    ltnled
    @3
    @6
    @5
    @3
    cA
    cC
    @8
    @0
    @1
    @2
    simp3
    #
    resubcld
    @3
    cB
    cC
    @9
    @10
    resubcld
    ltnled
    3bitr4d
end
