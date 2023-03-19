include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "rpcn.mm"
include "mulid2d.mm"
include "eqcomd.mm"
include "adantr.mm"
include "breq1d.mm"
include "cc0.mm"
include "clt.mm"
include "wb.mm"
include "1red.mm"
include "simpr.mm"
include "rpregt0.mm"
include "lemuldiv.mm"
include "syl3anc.mm"
include "bitrd.mm"

theorem divge1b
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR+ /\ B e. RR ) -> ( A <_ B <-> 1 <_ ( B / A ) ) )

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
    cle
    wbr
    c1
    cA
    cmul
    co
    #
    cB
    cle
    wbr
    #
    c1
    cB
    cA
    cdiv
    co
    cle
    wbr
    #
    @2
    cA
    @3
    cB
    cle
    @0
    cA
    @3
    wceq
    @1
    @0
    @3
    cA
    @0
    cA
    cA
    rpcn
    mulid2d
    eqcomd
    adantr
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
    lemuldiv
    syl3anc
    bitrd
end
