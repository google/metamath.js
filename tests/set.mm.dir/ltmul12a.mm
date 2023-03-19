include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cmul.mm"
include "co.mm"
include "simplll.mm"
include "simpllr.mm"
include "simpll.mm"
include "simprl.mm"
include "jca.mm"
include "ad2ant2l.mm"
include "ltle.mm"
include "imp.mm"
include "adantrl.mm"
include "ad2ant2r.mm"
include "lemul1a.mm"
include "syl31anc.mm"
include "wb.mm"
include "simplrl.mm"
include "simplrr.mm"
include "wi.mm"
include "0re.mm"
include "lelttr.mm"
include "mp3an1.mm"
include "adantlr.mm"
include "ltmul2.mm"
include "syl112anc.mm"
include "biimpa.mm"
include "anasss.mm"
include "adantrrl.mm"
include "remulcl.mm"
include "ad2ant2lr.mm"
include "syl3anc.mm"
include "adantr.mm"
include "mp2and.mm"
include "an4s.mm"

theorem ltmul12a
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( ( A e. RR /\ B e. RR ) /\ ( 0 <_ A /\ A < B ) ) /\ ( ( C e. RR /\ D e. RR ) /\ ( 0 <_ C /\ C < D ) ) ) -> ( A x. C ) < ( B x. D ) )

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
    cc0
    cA
    cle
    wbr
    #
    cA
    cB
    clt
    wbr
    #
    wa
    #
    cc0
    cC
    cle
    wbr
    #
    cC
    cD
    clt
    wbr
    #
    wa
    #
    cA
    cC
    cmul
    co
    #
    cB
    cD
    cmul
    co
    #
    clt
    wbr
    #
    @2
    @5
    wa
    #
    @8
    @11
    wa
    #
    wa
    #
    @12
    cB
    cC
    cmul
    co
    #
    cle
    wbr
    #
    @18
    @13
    clt
    wbr
    #
    @14
    @17
    @0
    @1
    @3
    @9
    wa
    #
    cA
    cB
    cle
    wbr
    #
    @19
    @0
    @1
    @5
    @16
    simplll
    @0
    @1
    @5
    @16
    simpllr
    @5
    @11
    @21
    @2
    @8
    @5
    @11
    wa
    @3
    @9
    @3
    @4
    @11
    simpll
    @5
    @9
    @10
    simprl
    jca
    ad2ant2l
    @2
    @8
    @22
    @5
    @11
    @2
    @7
    @22
    @6
    @2
    @7
    @22
    cA
    cB
    ltle
    imp
    adantrl
    ad2ant2r
    cA
    cB
    cC
    lemul1a
    syl31anc
    @15
    @8
    @10
    @20
    @9
    @15
    @8
    @10
    @20
    @15
    @8
    wa
    #
    @10
    @20
    @23
    @3
    @4
    @1
    cc0
    cB
    clt
    wbr
    #
    @10
    @20
    wb
    @2
    @3
    @4
    @8
    simplrl
    @2
    @3
    @4
    @8
    simplrr
    @0
    @1
    @5
    @8
    simpllr
    @2
    @8
    @24
    @5
    @2
    @8
    @24
    cc0
    cr
    wcel
    @0
    @1
    @8
    @24
    wi
    0re
    cc0
    cA
    cB
    lelttr
    mp3an1
    imp
    adantlr
    cC
    cD
    cB
    ltmul2
    syl112anc
    biimpa
    anasss
    adantrrl
    @15
    @19
    @20
    wa
    @14
    wi
    #
    @16
    @15
    @12
    cr
    wcel
    #
    @18
    cr
    wcel
    #
    @13
    cr
    wcel
    #
    @25
    @0
    @3
    @26
    @1
    @4
    cA
    cC
    remulcl
    ad2ant2r
    @1
    @3
    @27
    @0
    @4
    cB
    cC
    remulcl
    ad2ant2lr
    @1
    @4
    @28
    @0
    @3
    cB
    cD
    remulcl
    ad2ant2l
    @12
    @18
    @13
    lelttr
    syl3anc
    adantr
    mp2and
    an4s
end
