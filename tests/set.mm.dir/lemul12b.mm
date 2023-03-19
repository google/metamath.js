include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "wi.mm"
include "w3a.mm"
include "lemul2a.mm"
include "ex.mm"
include "3comr.mm"
include "3expb.mm"
include "adantrrr.mm"
include "adantlr.mm"
include "lemul1a.mm"
include "3expa.mm"
include "adantllr.mm"
include "adantrl.mm"
include "anim12d.mm"
include "ancomsd.mm"
include "remulcl.mm"
include "ad2ant2r.mm"
include "ad2ant2rl.mm"
include "adantrr.mm"
include "ad2ant2l.mm"
include "letr.mm"
include "syl3anc.mm"
include "syld.mm"

theorem lemul12b
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( ( A e. RR /\ 0 <_ A ) /\ B e. RR ) /\ ( C e. RR /\ ( D e. RR /\ 0 <_ D ) ) ) -> ( ( A <_ B /\ C <_ D ) -> ( A x. C ) <_ ( B x. D ) ) )

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
    wa
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
    cc0
    cD
    cle
    wbr
    #
    wa
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
    cA
    cC
    cmul
    co
    #
    cA
    cD
    cmul
    co
    #
    cle
    wbr
    #
    @14
    cB
    cD
    cmul
    co
    #
    cle
    wbr
    #
    wa
    #
    @13
    @16
    cle
    wbr
    #
    @10
    @12
    @11
    @18
    @10
    @12
    @15
    @11
    @17
    @2
    @9
    @12
    @15
    wi
    #
    @3
    @2
    @5
    @6
    @20
    @7
    @2
    @5
    @6
    @20
    @5
    @6
    @2
    @20
    @5
    @6
    @2
    w3a
    @12
    @15
    cC
    cD
    cA
    lemul2a
    ex
    3comr
    3expb
    adantrrr
    adantlr
    @4
    @8
    @11
    @17
    wi
    #
    @5
    @0
    @3
    @8
    @21
    @1
    @0
    @3
    @8
    @21
    @0
    @3
    @8
    w3a
    @11
    @17
    cA
    cB
    cD
    lemul1a
    ex
    3expa
    adantllr
    adantrl
    anim12d
    ancomsd
    @10
    @13
    cr
    wcel
    #
    @14
    cr
    wcel
    #
    @16
    cr
    wcel
    #
    @18
    @19
    wi
    @2
    @5
    @22
    @3
    @8
    @0
    @5
    @22
    @1
    cA
    cC
    remulcl
    adantlr
    ad2ant2r
    @2
    @8
    @23
    @3
    @5
    @0
    @6
    @23
    @1
    @7
    cA
    cD
    remulcl
    ad2ant2r
    ad2ant2rl
    @3
    @8
    @24
    @2
    @5
    @3
    @6
    @24
    @7
    cB
    cD
    remulcl
    adantrr
    ad2ant2l
    @13
    @14
    @16
    letr
    syl3anc
    syld
end
