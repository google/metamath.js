include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cneg.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "subcl.mm"
include "absneg.mm"
include "syl.mm"
include "negsubdi2.mm"
include "fveq2d.mm"
include "eqtr3d.mm"

theorem abssub
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( abs ` ( A - B ) ) = ( abs ` ( B - A ) ) )

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
    cabs
    cfv
    #
    @1
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
    absneg
    syl
    @0
    @2
    @5
    cabs
    cA
    cB
    negsubdi2
    fveq2d
    eqtr3d
end
