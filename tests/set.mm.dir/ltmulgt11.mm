include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "wb.mm"
include "wa.mm"
include "1re.mm"
include "ltmul2.mm"
include "mp3an1.mm"
include "3impb.mm"
include "3com12.mm"
include "wceq.mm"
include "ax-1rid.mm"
include "3ad2ant1.mm"
include "breq1d.mm"
include "bitrd.mm"

theorem ltmulgt11
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR /\ 0 < A ) -> ( 1 < B <-> A < ( A x. B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    w3a
    #
    c1
    cB
    clt
    wbr
    #
    cA
    c1
    cmul
    co
    #
    cA
    cB
    cmul
    co
    #
    clt
    wbr
    #
    cA
    @6
    clt
    wbr
    @1
    @0
    @2
    @4
    @7
    wb
    #
    @1
    @0
    @2
    @8
    c1
    cr
    wcel
    @1
    @0
    @2
    wa
    @8
    1re
    c1
    cB
    cA
    ltmul2
    mp3an1
    3impb
    3com12
    @3
    @5
    cA
    @6
    clt
    @0
    @1
    @5
    cA
    wceq
    @2
    cA
    ax-1rid
    3ad2ant1
    breq1d
    bitrd
end
