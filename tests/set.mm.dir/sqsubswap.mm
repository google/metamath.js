include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cneg.mm"
include "c2.mm"
include "cexp.mm"
include "wceq.mm"
include "subcl.mm"
include "sqneg.mm"
include "syl.mm"
include "negsubdi2.mm"
include "oveq1d.mm"
include "eqtr3d.mm"

theorem sqsubswap
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A - B ) ^ 2 ) = ( ( B - A ) ^ 2 ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    wa
    #
    cA
    cB
    cmin
    co
    #
    cneg
    #
    c2
    cexp
    co
    #
    @1
    c2
    cexp
    co
    #
    cB
    cA
    cmin
    co
    #
    c2
    cexp
    co
    @0
    @1
    cc
    wcel
    @3
    @4
    wceq
    cA
    cB
    subcl
    @1
    sqneg
    syl
    @0
    @2
    @5
    c2
    cexp
    cA
    cB
    negsubdi2
    oveq1d
    eqtr3d
end
