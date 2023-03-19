include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "wb.mm"
include "wne.mm"
include "gt0ne0.mm"
include "rereccl.mm"
include "syldan.mm"
include "recgt0.mm"
include "jca.mm"
include "lerec.mm"
include "sylan2.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "recrec.mm"
include "sylan.mm"
include "adantl.mm"
include "breq1d.mm"
include "bitrd.mm"

theorem lerec2
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 < A ) /\ ( B e. RR /\ 0 < B ) ) -> ( A <_ ( 1 / B ) <-> B <_ ( 1 / A ) ) )

  proof
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    wa
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    clt
    wbr
    #
    wa
    #
    wa
    #
    cA
    c1
    cB
    cdiv
    co
    #
    cle
    wbr
    #
    c1
    @5
    cdiv
    co
    #
    c1
    cA
    cdiv
    co
    #
    cle
    wbr
    #
    cB
    @8
    cle
    wbr
    @3
    @0
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
    @6
    @9
    wb
    @3
    @10
    @11
    @1
    @2
    cB
    cc0
    wne
    #
    @10
    cB
    gt0ne0
    #
    cB
    rereccl
    syldan
    cB
    recgt0
    jca
    cA
    @5
    lerec
    sylan2
    @4
    @7
    cB
    @8
    cle
    @3
    @7
    cB
    wceq
    #
    @0
    @1
    @2
    @12
    @14
    @13
    @1
    cB
    cc
    wcel
    @12
    @14
    cB
    recn
    cB
    recrec
    sylan
    syldan
    adantl
    breq1d
    bitrd
end
