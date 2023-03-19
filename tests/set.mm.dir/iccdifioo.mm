include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cicc.mm"
include "co.mm"
include "cioo.mm"
include "cdif.mm"
include "cpr.mm"
include "cun.mm"
include "uncom.mm"
include "prunioo.mm"
include "syl5reqr.mm"
include "difeq1d.mm"
include "wceq.mm"
include "difun2.mm"
include "a1i.mm"
include "cin.mm"
include "c0.mm"
include "incom.mm"
include "iooinlbub.mm"
include "eqtr3i.mm"
include "disj3.mm"
include "mpbi.mm"
include "eqcomi.mm"
include "3eqtrd.mm"

theorem iccdifioo
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* /\ A <_ B ) -> ( ( A [,] B ) \ ( A (,) B ) ) = { A , B } )

  proof
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cA
    cB
    cle
    wbr
    w3a
    #
    cA
    cB
    cicc
    co
    #
    cA
    cB
    cioo
    co
    #
    cdif
    cA
    cB
    cpr
    #
    @2
    cun
    #
    @2
    cdif
    #
    @3
    @2
    cdif
    #
    @3
    @0
    @1
    @4
    @2
    @0
    @4
    @2
    @3
    cun
    @1
    @2
    @3
    uncom
    cA
    cB
    prunioo
    syl5reqr
    difeq1d
    @5
    @6
    wceq
    @0
    @3
    @2
    difun2
    a1i
    @6
    @3
    wceq
    @0
    @3
    @6
    @3
    @2
    cin
    #
    c0
    wceq
    @3
    @6
    wceq
    @2
    @3
    cin
    @7
    c0
    @2
    @3
    incom
    cA
    cB
    iooinlbub
    eqtr3i
    @3
    @2
    disj3
    mpbi
    eqcomi
    a1i
    3eqtrd
end
