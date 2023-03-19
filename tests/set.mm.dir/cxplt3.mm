include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "cdiv.mm"
include "co.mm"
include "ccxp.mm"
include "cc.mm"
include "wceq.mm"
include "simpll.mm"
include "simprl.mm"
include "recnd.mm"
include "cxprec.mm"
include "syl2anc.mm"
include "simprr.mm"
include "breq12d.mm"
include "wb.mm"
include "rprecred.mm"
include "simplr.mm"
include "reclt1d.mm"
include "mpbid.mm"
include "cxplt.mm"
include "syl22anc.mm"
include "rpcxpcl.mm"
include "ad2ant2rl.mm"
include "ad2ant2r.mm"
include "ltrecd.mm"
include "3bitr4d.mm"

theorem cxplt3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR+ /\ A < 1 ) /\ ( B e. RR /\ C e. RR ) ) -> ( B < C <-> ( A ^c C ) < ( A ^c B ) ) )

  proof
    cA
    crp
    wcel
    #
    cA
    c1
    clt
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    wa
    #
    wa
    #
    c1
    cA
    cdiv
    co
    #
    cB
    ccxp
    co
    #
    @7
    cC
    ccxp
    co
    #
    clt
    wbr
    #
    c1
    cA
    cB
    ccxp
    co
    #
    cdiv
    co
    #
    c1
    cA
    cC
    ccxp
    co
    #
    cdiv
    co
    #
    clt
    wbr
    cB
    cC
    clt
    wbr
    #
    @13
    @11
    clt
    wbr
    @6
    @8
    @12
    @9
    @14
    clt
    @6
    @0
    cB
    cc
    wcel
    @8
    @12
    wceq
    @0
    @1
    @5
    simpll
    #
    @6
    cB
    @2
    @3
    @4
    simprl
    #
    recnd
    cA
    cB
    cxprec
    syl2anc
    @6
    @0
    cC
    cc
    wcel
    @9
    @14
    wceq
    @16
    @6
    cC
    @2
    @3
    @4
    simprr
    #
    recnd
    cA
    cC
    cxprec
    syl2anc
    breq12d
    @6
    @7
    cr
    wcel
    c1
    @7
    clt
    wbr
    #
    @3
    @4
    @15
    @10
    wb
    @6
    cA
    @16
    rprecred
    @6
    @1
    @19
    @0
    @1
    @5
    simplr
    @6
    cA
    @16
    reclt1d
    mpbid
    @17
    @18
    @7
    cB
    cC
    cxplt
    syl22anc
    @6
    @13
    @11
    @0
    @4
    @13
    crp
    wcel
    @1
    @3
    cA
    cC
    rpcxpcl
    ad2ant2rl
    @0
    @3
    @11
    crp
    wcel
    @1
    @4
    cA
    cB
    rpcxpcl
    ad2ant2r
    ltrecd
    3bitr4d
end
