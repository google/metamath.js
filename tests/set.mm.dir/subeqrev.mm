include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cneg.mm"
include "wceq.mm"
include "wb.mm"
include "subcl.mm"
include "neg11.mm"
include "syl2an.mm"
include "negsubdi2.mm"
include "eqeqan12d.mm"
include "bitr3d.mm"

theorem subeqrev
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( C e. CC /\ D e. CC ) ) -> ( ( A - B ) = ( C - D ) <-> ( B - A ) = ( D - C ) ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    wa
    #
    cC
    cc
    wcel
    cD
    cc
    wcel
    wa
    #
    wa
    cA
    cB
    cmin
    co
    #
    cneg
    #
    cC
    cD
    cmin
    co
    #
    cneg
    #
    wceq
    #
    @2
    @4
    wceq
    #
    cB
    cA
    cmin
    co
    #
    cD
    cC
    cmin
    co
    #
    wceq
    @0
    @2
    cc
    wcel
    @4
    cc
    wcel
    @6
    @7
    wb
    @1
    cA
    cB
    subcl
    cC
    cD
    subcl
    @2
    @4
    neg11
    syl2an
    @0
    @1
    @3
    @8
    @5
    @9
    cA
    cB
    negsubdi2
    cC
    cD
    negsubdi2
    eqeqan12d
    bitr3d
end
