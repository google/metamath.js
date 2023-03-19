include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "abssub.mm"
include "syl2an.mm"
include "3adant3.mm"
include "abssubge0.mm"
include "eqtrd.mm"

theorem abssuble0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR /\ A <_ B ) -> ( abs ` ( A - B ) ) = ( B - A ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    w3a
    cA
    cB
    cmin
    co
    cabs
    cfv
    #
    cB
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @4
    @0
    @1
    @3
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
    abssub
    syl2an
    3adant3
    cA
    cB
    abssubge0
    eqtrd
end
