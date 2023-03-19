include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "wb.mm"
include "simpll.mm"
include "simprl.mm"
include "simplr.mm"
include "leadd1.mm"
include "syl3anc.mm"
include "simprr.mm"
include "leadd2.mm"
include "anbi12d.mm"
include "wi.mm"
include "readdcld.mm"
include "letr.mm"
include "sylbid.mm"

theorem le2add
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( C e. RR /\ D e. RR ) ) -> ( ( A <_ C /\ B <_ D ) -> ( A + B ) <_ ( C + D ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cC
    cr
    wcel
    #
    cD
    cr
    wcel
    #
    wa
    #
    wa
    #
    cA
    cC
    cle
    wbr
    #
    cB
    cD
    cle
    wbr
    #
    wa
    cA
    cB
    caddc
    co
    #
    cC
    cB
    caddc
    co
    #
    cle
    wbr
    #
    @10
    cC
    cD
    caddc
    co
    #
    cle
    wbr
    #
    wa
    #
    @9
    @12
    cle
    wbr
    #
    @6
    @7
    @11
    @8
    @13
    @6
    @0
    @3
    @1
    @7
    @11
    wb
    @0
    @1
    @5
    simpll
    #
    @2
    @3
    @4
    simprl
    #
    @0
    @1
    @5
    simplr
    #
    cA
    cC
    cB
    leadd1
    syl3anc
    @6
    @1
    @4
    @3
    @8
    @13
    wb
    @18
    @2
    @3
    @4
    simprr
    #
    @17
    cB
    cD
    cC
    leadd2
    syl3anc
    anbi12d
    @6
    @9
    cr
    wcel
    @10
    cr
    wcel
    @12
    cr
    wcel
    @14
    @15
    wi
    @6
    cA
    cB
    @16
    @18
    readdcld
    @6
    cC
    cB
    @17
    @18
    readdcld
    @6
    cC
    cD
    @17
    @19
    readdcld
    @9
    @10
    @12
    letr
    syl3anc
    sylbid
end
