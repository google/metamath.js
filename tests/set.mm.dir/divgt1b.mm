include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "cc.mm"
include "rpcn.mm"
include "adantr.mm"
include "mulid2d.mm"
include "eqcomd.mm"
include "breq1d.mm"
include "cc0.mm"
include "wb.mm"
include "1red.mm"
include "simpr.mm"
include "rpregt0.mm"
include "ltmuldiv.mm"
include "syl3anc.mm"
include "bitrd.mm"

theorem divgt1b
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR+ /\ B e. RR ) -> ( A < B <-> 1 < ( B / A ) ) )

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
    clt
    wbr
    c1
    cA
    cmul
    co
    #
    cB
    clt
    wbr
    #
    c1
    cB
    cA
    cdiv
    co
    clt
    wbr
    #
    @2
    cA
    @3
    cB
    clt
    @2
    @3
    cA
    @2
    cA
    @0
    cA
    cc
    wcel
    @1
    cA
    rpcn
    adantr
    mulid2d
    eqcomd
    breq1d
    @2
    c1
    cr
    wcel
    @1
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    wa
    #
    @4
    @5
    wb
    @2
    1red
    @0
    @1
    simpr
    @0
    @6
    @1
    cA
    rpregt0
    adantr
    c1
    cB
    cA
    ltmuldiv
    syl3anc
    bitrd
end
