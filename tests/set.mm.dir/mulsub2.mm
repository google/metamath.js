include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cneg.mm"
include "cmul.mm"
include "wceq.mm"
include "subcl.mm"
include "mul2neg.mm"
include "syl2an.mm"
include "negsubdi2.mm"
include "oveqan12d.mm"
include "eqtr3d.mm"

theorem mulsub2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( C e. CC /\ D e. CC ) ) -> ( ( A - B ) x. ( C - D ) ) = ( ( B - A ) x. ( D - C ) ) )

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
    cmul
    co
    #
    @2
    @4
    cmul
    co
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
    cmul
    co
    @0
    @2
    cc
    wcel
    @4
    cc
    wcel
    @6
    @7
    wceq
    @1
    cA
    cB
    subcl
    cC
    cD
    subcl
    @2
    @4
    mul2neg
    syl2an
    @0
    @1
    @3
    @8
    @5
    @9
    cmul
    cA
    cB
    negsubdi2
    cC
    cD
    negsubdi2
    oveqan12d
    eqtr3d
end
