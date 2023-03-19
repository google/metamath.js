include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wb.mm"
include "wne.mm"
include "gt0ne0.mm"
include "rereccl.mm"
include "syldan.mm"
include "recgt0.mm"
include "jca.mm"
include "ltrec.mm"
include "sylan.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "recrec.mm"
include "adantr.mm"
include "breq2d.mm"
include "bitrd.mm"

theorem ltrec1
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 < A ) /\ ( B e. RR /\ 0 < B ) ) -> ( ( 1 / A ) < B <-> ( 1 / B ) < A ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    cc0
    cB
    clt
    wbr
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
    clt
    wbr
    #
    c1
    cB
    cdiv
    co
    #
    c1
    @5
    cdiv
    co
    #
    clt
    wbr
    #
    @7
    cA
    clt
    wbr
    @2
    @5
    cr
    wcel
    #
    cc0
    @5
    clt
    wbr
    #
    wa
    @3
    @6
    @9
    wb
    @2
    @10
    @11
    @0
    @1
    cA
    cc0
    wne
    #
    @10
    cA
    gt0ne0
    #
    cA
    rereccl
    syldan
    cA
    recgt0
    jca
    @5
    cB
    ltrec
    sylan
    @4
    @8
    cA
    @7
    clt
    @2
    @8
    cA
    wceq
    #
    @3
    @0
    @1
    @12
    @14
    @13
    @0
    cA
    cc
    wcel
    @12
    @14
    cA
    recn
    cA
    recrec
    sylan
    syldan
    adantr
    breq2d
    bitrd
end
