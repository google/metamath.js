include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "wn.mm"
include "ccxp.mm"
include "co.mm"
include "cle.mm"
include "wb.mm"
include "cxplt3.mm"
include "ancom2s.mm"
include "notbid.mm"
include "lenlt.mm"
include "adantl.mm"
include "rpcxpcl.mm"
include "ad2ant2rl.mm"
include "ad2ant2r.mm"
include "rpre.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "3bitr4d.mm"

theorem cxple3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR+ /\ A < 1 ) /\ ( B e. RR /\ C e. RR ) ) -> ( B <_ C <-> ( A ^c C ) <_ ( A ^c B ) ) )

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
    cC
    cB
    clt
    wbr
    #
    wn
    #
    cA
    cB
    ccxp
    co
    #
    cA
    cC
    ccxp
    co
    #
    clt
    wbr
    #
    wn
    #
    cB
    cC
    cle
    wbr
    #
    @10
    @9
    cle
    wbr
    #
    @6
    @7
    @11
    @2
    @4
    @3
    @7
    @11
    wb
    cA
    cC
    cB
    cxplt3
    ancom2s
    notbid
    @5
    @13
    @8
    wb
    @2
    cB
    cC
    lenlt
    adantl
    @6
    @10
    crp
    wcel
    #
    @9
    crp
    wcel
    #
    @14
    @12
    wb
    #
    @0
    @4
    @15
    @1
    @3
    cA
    cC
    rpcxpcl
    ad2ant2rl
    @0
    @3
    @16
    @1
    @4
    cA
    cB
    rpcxpcl
    ad2ant2r
    @15
    @10
    cr
    wcel
    @9
    cr
    wcel
    @17
    @16
    @10
    rpre
    @9
    rpre
    @10
    @9
    lenlt
    syl2an
    syl2anc
    3bitr4d
end
