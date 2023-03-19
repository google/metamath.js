include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cxad.mm"
include "co.mm"
include "wi.mm"
include "simpll.mm"
include "simprl.mm"
include "simplr.mm"
include "w3a.mm"
include "xleadd1a.mm"
include "ex.mm"
include "syl3anc.mm"
include "simprr.mm"
include "xleadd2a.mm"
include "xaddcl.mm"
include "adantr.mm"
include "syl2anc.mm"
include "adantl.mm"
include "xrletr.mm"
include "syl2and.mm"

theorem xle2add
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. RR* /\ B e. RR* ) /\ ( C e. RR* /\ D e. RR* ) ) -> ( ( A <_ C /\ B <_ D ) -> ( A +e B ) <_ ( C +e D ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cC
    cxr
    wcel
    #
    cD
    cxr
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
    cA
    cB
    cxad
    co
    #
    cC
    cB
    cxad
    co
    #
    cle
    wbr
    #
    cB
    cD
    cle
    wbr
    #
    @9
    cC
    cD
    cxad
    co
    #
    cle
    wbr
    #
    @8
    @12
    cle
    wbr
    #
    @6
    @0
    @3
    @1
    @7
    @10
    wi
    @0
    @1
    @5
    simpll
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
    @0
    @3
    @1
    w3a
    @7
    @10
    cA
    cC
    cB
    xleadd1a
    ex
    syl3anc
    @6
    @1
    @4
    @3
    @11
    @13
    wi
    @16
    @2
    @3
    @4
    simprr
    @15
    @1
    @4
    @3
    w3a
    @11
    @13
    cB
    cD
    cC
    xleadd2a
    ex
    syl3anc
    @6
    @8
    cxr
    wcel
    #
    @9
    cxr
    wcel
    #
    @12
    cxr
    wcel
    #
    @10
    @13
    wa
    @14
    wi
    @2
    @17
    @5
    cA
    cB
    xaddcl
    adantr
    @6
    @3
    @1
    @18
    @15
    @16
    cC
    cB
    xaddcl
    syl2anc
    @5
    @19
    @2
    cC
    cD
    xaddcl
    adantl
    @8
    @9
    @12
    xrletr
    syl3anc
    syl2and
end
