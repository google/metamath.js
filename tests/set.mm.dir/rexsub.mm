include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cxne.mm"
include "cxad.mm"
include "co.mm"
include "cneg.mm"
include "caddc.mm"
include "cmin.mm"
include "wceq.mm"
include "rexneg.mm"
include "adantl.mm"
include "oveq2d.mm"
include "renegcl.mm"
include "rexadd.mm"
include "sylan2.mm"
include "cc.mm"
include "recn.mm"
include "negsub.mm"
include "syl2an.mm"
include "3eqtrd.mm"

theorem rexsub
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A +e -e B ) = ( A - B ) )

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
    cA
    cB
    cxne
    #
    cxad
    co
    cA
    cB
    cneg
    #
    cxad
    co
    #
    cA
    @4
    caddc
    co
    #
    cA
    cB
    cmin
    co
    #
    @2
    @3
    @4
    cA
    cxad
    @1
    @3
    @4
    wceq
    @0
    cB
    rexneg
    adantl
    oveq2d
    @1
    @0
    @4
    cr
    wcel
    @5
    @6
    wceq
    cB
    renegcl
    cA
    @4
    rexadd
    sylan2
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @6
    @7
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
    3eqtrd
end
