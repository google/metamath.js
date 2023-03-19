include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "addcom.mm"
include "syl2an.mm"
include "3adant3.mm"
include "breq1d.mm"
include "wb.mm"
include "ltaddsub.mm"
include "3com12.mm"
include "bitrd.mm"

theorem ltaddsub2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( ( A + B ) < C <-> B < ( C - A ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    w3a
    #
    cA
    cB
    caddc
    co
    #
    cC
    clt
    wbr
    cB
    cA
    caddc
    co
    #
    cC
    clt
    wbr
    #
    cB
    cC
    cA
    cmin
    co
    clt
    wbr
    #
    @3
    @4
    @5
    cC
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
    @8
    @1
    cA
    recn
    cB
    recn
    cA
    cB
    addcom
    syl2an
    3adant3
    breq1d
    @1
    @0
    @2
    @6
    @7
    wb
    cB
    cA
    cC
    ltaddsub
    3com12
    bitrd
end
