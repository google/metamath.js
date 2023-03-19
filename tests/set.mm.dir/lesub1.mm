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
include "simp3.mm"
include "simp2.mm"
include "resubcld.mm"
include "lesubadd.mm"
include "syl3anc.mm"
include "recnd.mm"
include "npcand.mm"
include "breq2d.mm"
include "bitr2d.mm"

theorem lesub1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A <_ B <-> ( A - C ) <_ ( B - C ) ) )

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
    cC
    cmin
    co
    cB
    cC
    cmin
    co
    #
    cle
    wbr
    #
    cA
    @4
    cC
    caddc
    co
    #
    cle
    wbr
    #
    cA
    cB
    cle
    wbr
    @3
    @0
    @2
    @4
    cr
    wcel
    @5
    @7
    wb
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp3
    #
    @3
    cB
    cC
    @0
    @1
    @2
    simp2
    #
    @8
    resubcld
    cA
    cC
    @4
    lesubadd
    syl3anc
    @3
    @6
    cB
    cA
    cle
    @3
    cB
    cC
    @3
    cB
    @9
    recnd
    @3
    cC
    @8
    recnd
    npcand
    breq2d
    bitr2d
end
