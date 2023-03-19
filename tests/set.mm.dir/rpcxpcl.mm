include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "ccxp.mm"
include "co.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "rprege0.mm"
include "recxpcl.mm"
include "3expa.mm"
include "sylan.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "ce.mm"
include "clt.mm"
include "id.mm"
include "relogcl.mm"
include "remulcl.mm"
include "syl2anr.mm"
include "efgt0.mm"
include "syl.mm"
include "cc.mm"
include "wne.mm"
include "wceq.mm"
include "rpcnne0.mm"
include "recn.mm"
include "cxpef.mm"
include "syl2an.mm"
include "breqtrrd.mm"
include "elrpd.mm"

theorem rpcxpcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR+ /\ B e. RR ) -> ( A ^c B ) e. RR+ )

  proof
    cA
    crp
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    ccxp
    co
    #
    @0
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
    @1
    @3
    cr
    wcel
    #
    cA
    rprege0
    @4
    @5
    @1
    @6
    cA
    cB
    recxpcl
    3expa
    sylan
    @2
    cc0
    cB
    cA
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    @3
    clt
    @2
    @8
    cr
    wcel
    #
    cc0
    @9
    clt
    wbr
    @1
    @1
    @7
    cr
    wcel
    @10
    @0
    @1
    id
    cA
    relogcl
    cB
    @7
    remulcl
    syl2anr
    @8
    efgt0
    syl
    @0
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    cB
    cc
    wcel
    #
    @3
    @9
    wceq
    #
    @1
    cA
    rpcnne0
    cB
    recn
    @11
    @12
    @13
    @14
    cA
    cB
    cxpef
    3expa
    syl2an
    breqtrrd
    elrpd
end
