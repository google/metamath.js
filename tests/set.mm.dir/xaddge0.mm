include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cxad.mm"
include "co.mm"
include "0xr.mm"
include "a1i.mm"
include "simplr.mm"
include "xaddcl.mm"
include "adantr.mm"
include "simprr.mm"
include "wceq.mm"
include "xaddid2.mm"
include "syl.mm"
include "simpll.mm"
include "simprl.mm"
include "xleadd1a.mm"
include "syl31anc.mm"
include "eqbrtrrd.mm"
include "xrletrd.mm"

theorem xaddge0
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR* /\ B e. RR* ) /\ ( 0 <_ A /\ 0 <_ B ) ) -> 0 <_ ( A +e B ) )

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
    cc0
    cA
    cle
    wbr
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    wa
    #
    cc0
    cB
    cA
    cB
    cxad
    co
    #
    cc0
    cxr
    wcel
    #
    @6
    0xr
    a1i
    #
    @0
    @1
    @5
    simplr
    #
    @2
    @7
    cxr
    wcel
    @5
    cA
    cB
    xaddcl
    adantr
    @2
    @3
    @4
    simprr
    @6
    cc0
    cB
    cxad
    co
    #
    cB
    @7
    cle
    @6
    @1
    @11
    cB
    wceq
    @10
    cB
    xaddid2
    syl
    @6
    @8
    @0
    @1
    @3
    @11
    @7
    cle
    wbr
    @9
    @0
    @1
    @5
    simpll
    @10
    @2
    @3
    @4
    simprl
    cc0
    cA
    cB
    xleadd1a
    syl31anc
    eqbrtrrd
    xrletrd
end
