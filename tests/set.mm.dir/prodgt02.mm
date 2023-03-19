include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "clt.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "mulcom.mm"
include "syl2an.mm"
include "breq2d.mm"
include "biimpd.mm"
include "wi.mm"
include "prodgt0.mm"
include "ex.mm"
include "ancoms.mm"
include "sylan2d.mm"
include "imp.mm"

theorem prodgt02
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( 0 <_ B /\ 0 < ( A x. B ) ) ) -> 0 < A )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cc0
    cB
    cle
    wbr
    #
    cc0
    cA
    cB
    cmul
    co
    #
    clt
    wbr
    #
    wa
    cc0
    cA
    clt
    wbr
    #
    @2
    @5
    cc0
    cB
    cA
    cmul
    co
    #
    clt
    wbr
    #
    @3
    @6
    @2
    @5
    @8
    @2
    @4
    @7
    cc0
    clt
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @4
    @7
    wceq
    @1
    cA
    recn
    cB
    recn
    cA
    cB
    mulcom
    syl2an
    breq2d
    biimpd
    @1
    @0
    @3
    @8
    wa
    #
    @6
    wi
    @1
    @0
    wa
    @9
    @6
    cB
    cA
    prodgt0
    ex
    ancoms
    sylan2d
    imp
end
