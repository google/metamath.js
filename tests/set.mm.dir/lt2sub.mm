include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "wb.mm"
include "simpll.mm"
include "simprl.mm"
include "simplr.mm"
include "ltsub1.mm"
include "syl3anc.mm"
include "simprr.mm"
include "ltsub2.mm"
include "anbi12d.mm"
include "wi.mm"
include "resubcl.mm"
include "adantr.mm"
include "resubcld.mm"
include "adantl.mm"
include "lttr.mm"
include "sylbid.mm"

theorem lt2sub
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( C e. RR /\ D e. RR ) ) -> ( ( A < C /\ D < B ) -> ( A - B ) < ( C - D ) ) )

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
    #
    cA
    cC
    clt
    wbr
    #
    cD
    cB
    clt
    wbr
    #
    wa
    cA
    cB
    cmin
    co
    #
    cC
    cB
    cmin
    co
    #
    clt
    wbr
    #
    @10
    cC
    cD
    cmin
    co
    #
    clt
    wbr
    #
    wa
    #
    @9
    @12
    clt
    wbr
    #
    @6
    @7
    @11
    @8
    @13
    @6
    @0
    @3
    @1
    @7
    @11
    wb
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
    cA
    cC
    cB
    ltsub1
    syl3anc
    @6
    @4
    @1
    @3
    @8
    @13
    wb
    @2
    @3
    @4
    simprr
    @17
    @16
    cD
    cB
    cC
    ltsub2
    syl3anc
    anbi12d
    @6
    @9
    cr
    wcel
    #
    @10
    cr
    wcel
    @12
    cr
    wcel
    #
    @14
    @15
    wi
    @2
    @18
    @5
    cA
    cB
    resubcl
    adantr
    @6
    cC
    cB
    @16
    @17
    resubcld
    @5
    @19
    @2
    cC
    cD
    resubcl
    adantl
    @9
    @10
    @12
    lttr
    syl3anc
    sylbid
end
