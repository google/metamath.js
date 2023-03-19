include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "wb.mm"
include "simp1.mm"
include "simp2.mm"
include "resubcld.mm"
include "simp3.mm"
include "leadd1.mm"
include "syl3anc.mm"
include "recnd.mm"
include "npcand.mm"
include "breq1d.mm"
include "bitrd.mm"

theorem lesubadd
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( ( A - B ) <_ C <-> A <_ ( C + B ) ) )

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
    cmin
    co
    #
    cC
    cle
    wbr
    #
    @4
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
    cA
    @7
    cle
    wbr
    @3
    @4
    cr
    wcel
    @2
    @1
    @5
    @8
    wb
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
    resubcld
    @0
    @1
    @2
    simp3
    @10
    @4
    cC
    cB
    leadd1
    syl3anc
    @3
    @6
    cA
    @7
    cle
    @3
    cA
    cB
    @3
    cA
    @9
    recnd
    @3
    cB
    @10
    recnd
    npcand
    breq1d
    bitrd
end
