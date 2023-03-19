include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "ax-1rid.mm"
include "ad2antrr.mm"
include "simpll.mm"
include "simprl.mm"
include "jca.mm"
include "simplr.mm"
include "1re.mm"
include "0le1.mm"
include "pm3.2i.mm"
include "jctil.mm"
include "jca31.mm"
include "leid.mm"
include "simprr.mm"
include "lemul12a.mm"
include "sylc.mm"
include "eqbrtrrd.mm"

theorem lemulge11
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( 0 <_ A /\ 1 <_ B ) ) -> A <_ ( A x. B ) )

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
    cc0
    cA
    cle
    wbr
    #
    c1
    cB
    cle
    wbr
    #
    wa
    #
    wa
    #
    cA
    c1
    cmul
    co
    #
    cA
    cA
    cB
    cmul
    co
    #
    cle
    @0
    @7
    cA
    wceq
    @1
    @5
    cA
    ax-1rid
    ad2antrr
    @6
    @0
    @3
    wa
    #
    @0
    wa
    c1
    cr
    wcel
    #
    cc0
    c1
    cle
    wbr
    #
    wa
    #
    @1
    wa
    #
    wa
    cA
    cA
    cle
    wbr
    #
    @4
    wa
    @7
    @8
    cle
    wbr
    @6
    @9
    @0
    @13
    @6
    @0
    @3
    @0
    @1
    @5
    simpll
    #
    @2
    @3
    @4
    simprl
    jca
    @15
    @6
    @1
    @12
    @0
    @1
    @5
    simplr
    @10
    @11
    1re
    0le1
    pm3.2i
    jctil
    jca31
    @6
    @14
    @4
    @0
    @14
    @1
    @5
    cA
    leid
    ad2antrr
    @2
    @3
    @4
    simprr
    jca
    cA
    cA
    c1
    cB
    lemul12a
    sylc
    eqbrtrrd
end
