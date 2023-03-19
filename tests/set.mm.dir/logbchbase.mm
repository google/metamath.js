include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "clogb.mm"
include "wa.mm"
include "wceq.mm"
include "eldifsn.mm"
include "logcl.mm"
include "sylbi.mm"
include "3ad2ant3.mm"
include "3adant3.mm"
include "logccne0.mm"
include "jca.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "divcan7.mm"
include "syl3anc.mm"
include "cpr.mm"
include "eldifpr.mm"
include "logbval.mm"
include "sylanbr.mm"
include "3adant1.mm"
include "biimpri.mm"
include "syl2anr.mm"
include "oveq12d.mm"
include "3adant2.mm"
include "3eqtr4rd.mm"

theorem logbchbase
  let cA: class A
  let cB: class B
  let cX: class X


  assert |- ( ( ( A e. CC /\ A =/= 0 /\ A =/= 1 ) /\ ( B e. CC /\ B =/= 0 /\ B =/= 1 ) /\ X e. ( CC \ { 0 } ) ) -> ( A logb X ) = ( ( B logb X ) / ( B logb A ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cA
    c1
    wne
    #
    w3a
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    cB
    c1
    wne
    #
    w3a
    #
    cX
    cc
    cc0
    csn
    cdif
    #
    wcel
    #
    w3a
    #
    cX
    clog
    cfv
    #
    cB
    clog
    cfv
    #
    cdiv
    co
    #
    cA
    clog
    cfv
    #
    @12
    cdiv
    co
    #
    cdiv
    co
    #
    @11
    @14
    cdiv
    co
    #
    cB
    cX
    clogb
    co
    #
    cB
    cA
    clogb
    co
    #
    cdiv
    co
    cA
    cX
    clogb
    co
    #
    @10
    @11
    cc
    wcel
    #
    @14
    cc
    wcel
    #
    @14
    cc0
    wne
    #
    wa
    #
    @12
    cc
    wcel
    #
    @12
    cc0
    wne
    #
    wa
    #
    @16
    @17
    wceq
    @9
    @3
    @21
    @7
    @9
    cX
    cc
    wcel
    cX
    cc0
    wne
    wa
    @21
    cX
    cc
    cc0
    eldifsn
    cX
    logcl
    sylbi
    3ad2ant3
    @3
    @7
    @24
    @9
    @3
    @22
    @23
    @0
    @1
    @22
    @2
    cA
    logcl
    3adant3
    cA
    logccne0
    jca
    3ad2ant1
    @7
    @3
    @27
    @9
    @7
    @25
    @26
    @4
    @5
    @25
    @6
    cB
    logcl
    3adant3
    cB
    logccne0
    jca
    3ad2ant2
    @11
    @14
    @12
    divcan7
    syl3anc
    @10
    @18
    @13
    @19
    @15
    cdiv
    @7
    @9
    @18
    @13
    wceq
    #
    @3
    @7
    cB
    cc
    cc0
    c1
    cpr
    cdif
    #
    wcel
    #
    @9
    @28
    cB
    cc
    cc0
    c1
    eldifpr
    #
    cB
    cX
    logbval
    sylanbr
    3adant1
    @3
    @7
    @19
    @15
    wceq
    #
    @9
    @7
    @30
    cA
    @8
    wcel
    #
    @32
    @3
    @30
    @7
    @31
    biimpri
    @0
    @1
    @33
    @2
    @33
    @0
    @1
    wa
    cA
    cc
    cc0
    eldifsn
    biimpri
    3adant3
    cB
    cA
    logbval
    syl2anr
    3adant3
    oveq12d
    @3
    @9
    @20
    @17
    wceq
    #
    @7
    @3
    cA
    @29
    wcel
    @9
    @34
    cA
    cc
    cc0
    c1
    eldifpr
    cA
    cX
    logbval
    sylanbr
    3adant2
    3eqtr4rd
end
