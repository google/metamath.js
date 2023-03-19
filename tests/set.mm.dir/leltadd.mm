include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "caddc.mm"
include "co.mm"
include "wi.mm"
include "ltleadd.mm"
include "ancomsd.mm"
include "ancom2s.mm"
include "ancom1s.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "addcom.mm"
include "syl2an.mm"
include "breqan12d.mm"
include "sylibrd.mm"

theorem leltadd
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( C e. RR /\ D e. RR ) ) -> ( ( A <_ C /\ B < D ) -> ( A + B ) < ( C + D ) ) )

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
    cA
    cC
    cle
    wbr
    #
    cB
    cD
    clt
    wbr
    #
    wa
    #
    cB
    cA
    caddc
    co
    #
    cD
    cC
    caddc
    co
    #
    clt
    wbr
    #
    cA
    cB
    caddc
    co
    #
    cC
    cD
    caddc
    co
    #
    clt
    wbr
    @1
    @0
    @5
    @8
    @11
    wi
    #
    @1
    @0
    wa
    #
    @4
    @3
    @14
    @15
    @4
    @3
    wa
    wa
    @7
    @6
    @11
    cB
    cA
    cD
    cC
    ltleadd
    ancomsd
    ancom2s
    ancom1s
    @2
    @5
    @12
    @9
    @13
    @10
    clt
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @12
    @9
    wceq
    @1
    cA
    recn
    cB
    recn
    cA
    cB
    addcom
    syl2an
    @3
    cC
    cc
    wcel
    cD
    cc
    wcel
    @13
    @10
    wceq
    @4
    cC
    recn
    cD
    recn
    cC
    cD
    addcom
    syl2an
    breqan12d
    sylibrd
end
