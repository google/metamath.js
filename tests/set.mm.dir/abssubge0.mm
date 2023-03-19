include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cc0.mm"
include "resubcl.mm"
include "3adant3.mm"
include "subge0.mm"
include "biimp3ar.mm"
include "absid.mm"
include "syl2anc.mm"
include "3com12.mm"

theorem abssubge0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR /\ A <_ B ) -> ( abs ` ( B - A ) ) = ( B - A ) )

  proof
    cB
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    cmin
    co
    #
    cabs
    cfv
    @3
    wceq
    #
    @0
    @1
    @2
    w3a
    @3
    cr
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    @4
    @0
    @1
    @5
    @2
    cB
    cA
    resubcl
    3adant3
    @0
    @1
    @6
    @2
    cB
    cA
    subge0
    biimp3ar
    @3
    absid
    syl2anc
    3com12
end
