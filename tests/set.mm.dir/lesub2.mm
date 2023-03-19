include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "leadd2.mm"
include "wb.mm"
include "simp3.mm"
include "simp1.mm"
include "readdcld.mm"
include "simp2.mm"
include "lesubadd.mm"
include "syl3anc.mm"
include "recnd.mm"
include "addsubd.mm"
include "breq1d.mm"
include "3bitr2d.mm"
include "resubcld.mm"
include "leaddsub.mm"
include "bitrd.mm"

theorem lesub2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A <_ B <-> ( C - B ) <_ ( C - A ) ) )

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
    cA
    cB
    cle
    wbr
    #
    cC
    cB
    cmin
    co
    #
    cA
    caddc
    co
    #
    cC
    cle
    wbr
    #
    @5
    cC
    cA
    cmin
    co
    cle
    wbr
    #
    @3
    @4
    cC
    cA
    caddc
    co
    #
    cC
    cB
    caddc
    co
    cle
    wbr
    #
    @9
    cB
    cmin
    co
    #
    cC
    cle
    wbr
    #
    @7
    cA
    cB
    cC
    leadd2
    @3
    @9
    cr
    wcel
    @1
    @2
    @12
    @10
    wb
    @3
    cC
    cA
    @0
    @1
    @2
    simp3
    #
    @0
    @1
    @2
    simp1
    #
    readdcld
    @0
    @1
    @2
    simp2
    #
    @13
    @9
    cB
    cC
    lesubadd
    syl3anc
    @3
    @11
    @6
    cC
    cle
    @3
    cC
    cA
    cB
    @3
    cC
    @13
    recnd
    @3
    cA
    @14
    recnd
    @3
    cB
    @15
    recnd
    addsubd
    breq1d
    3bitr2d
    @3
    @5
    cr
    wcel
    @0
    @2
    @7
    @8
    wb
    @3
    cC
    cB
    @13
    @15
    resubcld
    @14
    @13
    @5
    cA
    cC
    leaddsub
    syl3anc
    bitrd
end
