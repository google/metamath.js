include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "simpll.mm"
include "ad2antlr.mm"
include "simplrr.mm"
include "wi.mm"
include "0re.mm"
include "letr.mm"
include "mp3an1.mm"
include "exp4b.mm"
include "com23.mm"
include "imp41.mm"
include "ad2ant2l.mm"
include "jca.mm"
include "jca32.mm"
include "simpr.mm"
include "lemul12b.mm"
include "sylc.mm"
include "ex.mm"

theorem lemul12a
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( ( A e. RR /\ 0 <_ A ) /\ B e. RR ) /\ ( ( C e. RR /\ 0 <_ C ) /\ D e. RR ) ) -> ( ( A <_ B /\ C <_ D ) -> ( A x. C ) <_ ( B x. D ) ) )

  proof
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    wa
    cB
    cr
    wcel
    wa
    #
    cC
    cr
    wcel
    #
    cc0
    cC
    cle
    wbr
    #
    wa
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
    cB
    cle
    wbr
    #
    cC
    cD
    cle
    wbr
    #
    wa
    #
    cA
    cC
    cmul
    co
    cB
    cD
    cmul
    co
    cle
    wbr
    #
    @6
    @9
    wa
    #
    @0
    @1
    @4
    cc0
    cD
    cle
    wbr
    #
    wa
    #
    wa
    wa
    @9
    @10
    @11
    @0
    @1
    @13
    @0
    @5
    @9
    simpll
    @5
    @1
    @0
    @9
    @1
    @2
    @4
    simpll
    ad2antlr
    @11
    @4
    @12
    @0
    @3
    @4
    @9
    simplrr
    @5
    @8
    @12
    @0
    @7
    @1
    @2
    @4
    @8
    @12
    @1
    @4
    @2
    @8
    @12
    wi
    @1
    @4
    @2
    @8
    @12
    cc0
    cr
    wcel
    @1
    @4
    @2
    @8
    wa
    @12
    wi
    0re
    cc0
    cC
    cD
    letr
    mp3an1
    exp4b
    com23
    imp41
    ad2ant2l
    jca
    jca32
    @6
    @9
    simpr
    cA
    cB
    cC
    cD
    lemul12b
    sylc
    ex
end
