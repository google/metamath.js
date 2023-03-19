include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cmin.mm"
include "wceq.mm"
include "mulm1.mm"
include "adantl.mm"
include "oveq2d.mm"
include "negsub.mm"
include "eqtrd.mm"

theorem addneg1mul
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( A + ( -u 1 x. B ) ) = ( A - B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    c1
    cneg
    cB
    cmul
    co
    #
    caddc
    co
    cA
    cB
    cneg
    #
    caddc
    co
    cA
    cB
    cmin
    co
    @2
    @3
    @4
    cA
    caddc
    @1
    @3
    @4
    wceq
    @0
    cB
    mulm1
    adantl
    oveq2d
    cA
    cB
    negsub
    eqtrd
end
