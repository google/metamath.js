include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "ltmulgt11.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "mulcom.mm"
include "syl2an.mm"
include "3adant3.mm"
include "breq2d.mm"
include "bitrd.mm"

theorem ltmulgt12
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR /\ 0 < A ) -> ( 1 < B <-> A < ( B x. A ) ) )

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
    cA
    cA
    cB
    cmul
    co
    #
    clt
    wbr
    cA
    cB
    cA
    cmul
    co
    #
    clt
    wbr
    cA
    cB
    ltmulgt11
    @3
    @4
    @5
    cA
    clt
    @0
    @1
    @4
    @5
    wceq
    #
    @2
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @6
    @1
    cA
    recn
    cB
    recn
    cA
    cB
    mulcom
    syl2an
    3adant3
    breq2d
    bitrd
end
