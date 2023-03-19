include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "negsub.mm"
include "syl2an.mm"
include "renegcl.mm"
include "readdcl.mm"
include "sylan2.mm"
include "eqeltrrd.mm"

theorem resubcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A - B ) e. RR )

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
    cA
    cB
    cneg
    #
    caddc
    co
    #
    cA
    cB
    cmin
    co
    #
    cr
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @3
    @4
    wceq
    @1
    cA
    recn
    cB
    recn
    cA
    cB
    negsub
    syl2an
    @1
    @0
    @2
    cr
    wcel
    @3
    cr
    wcel
    cB
    renegcl
    cA
    @2
    readdcl
    sylan2
    eqeltrrd
end
