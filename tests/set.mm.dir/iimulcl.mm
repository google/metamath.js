include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "w3a.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cicc.mm"
include "remulcl.mm"
include "3ad2antr1.mm"
include "3ad2antl1.mm"
include "mulge0.mm"
include "3adantr3.mm"
include "3adantl3.mm"
include "an6.mm"
include "wi.mm"
include "1re.mm"
include "lemul12a.mm"
include "mpanr2.mm"
include "mpanl2.mm"
include "an4s.mm"
include "3impia.mm"
include "sylbi.mm"
include "1t1e1.mm"
include "syl6breq.mm"
include "3jca.mm"
include "0re.mm"
include "elicc2i.mm"
include "anbi12i.mm"
include "3imtr4i.mm"

theorem iimulcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ( 0 [,] 1 ) /\ B e. ( 0 [,] 1 ) ) -> ( A x. B ) e. ( 0 [,] 1 ) )

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
    cA
    c1
    cle
    wbr
    #
    w3a
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
    cB
    c1
    cle
    wbr
    #
    w3a
    #
    wa
    #
    cA
    cB
    cmul
    co
    #
    cr
    wcel
    #
    cc0
    @9
    cle
    wbr
    #
    @9
    c1
    cle
    wbr
    #
    w3a
    cA
    cc0
    c1
    cicc
    co
    #
    wcel
    #
    cB
    @13
    wcel
    #
    wa
    @9
    @13
    wcel
    @8
    @10
    @11
    @12
    @0
    @1
    @7
    @10
    @2
    @0
    @5
    @4
    @10
    @6
    cA
    cB
    remulcl
    3ad2antr1
    3ad2antl1
    @0
    @1
    @7
    @11
    @2
    @0
    @1
    wa
    #
    @4
    @5
    @11
    @6
    cA
    cB
    mulge0
    3adantr3
    3adantl3
    @8
    @9
    c1
    c1
    cmul
    co
    #
    c1
    cle
    @8
    @0
    @4
    wa
    #
    @1
    @5
    wa
    #
    @2
    @6
    wa
    #
    w3a
    @9
    @17
    cle
    wbr
    #
    @0
    @1
    @2
    @4
    @5
    @6
    an6
    @18
    @19
    @20
    @21
    @0
    @1
    @4
    @5
    @20
    @21
    wi
    #
    @16
    c1
    cr
    wcel
    #
    @4
    @5
    wa
    #
    @22
    1re
    @16
    @23
    wa
    @24
    @23
    @22
    1re
    cA
    c1
    cB
    c1
    lemul12a
    mpanr2
    mpanl2
    an4s
    3impia
    sylbi
    1t1e1
    syl6breq
    3jca
    @14
    @3
    @15
    @7
    cc0
    c1
    cA
    0re
    1re
    elicc2i
    cc0
    c1
    cB
    0re
    1re
    elicc2i
    anbi12i
    cc0
    c1
    @9
    0re
    1re
    elicc2i
    3imtr4i
end
