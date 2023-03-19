include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wb.mm"
include "ltadd1.mm"
include "3com12.mm"
include "notbid.mm"
include "simp1.mm"
include "simp2.mm"
include "lenltd.mm"
include "simp3.mm"
include "readdcld.mm"
include "3bitr4d.mm"

theorem leadd1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A <_ B <-> ( A + C ) <_ ( B + C ) ) )

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
    clt
    wbr
    #
    wn
    cB
    cC
    caddc
    co
    #
    cA
    cC
    caddc
    co
    #
    clt
    wbr
    #
    wn
    cA
    cB
    cle
    wbr
    @6
    @5
    cle
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
    ltadd1
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
    lenltd
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
    readdcld
    @3
    cB
    cC
    @9
    @10
    readdcld
    lenltd
    3bitr4d
end
