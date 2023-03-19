include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cneg.mm"
include "cdiv.mm"
include "cc0.mm"
include "wceq.mm"
include "subcl.mm"
include "3adant3.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "biimp3ar.mm"
include "jca.mm"
include "div2neg.mm"
include "3expb.mm"
include "syl2an.mm"
include "negsubdi2.mm"
include "oveqan12d.mm"
include "eqtr3d.mm"

theorem div2sub
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( C e. CC /\ D e. CC /\ C =/= D ) ) -> ( ( A - B ) / ( C - D ) ) = ( ( B - A ) / ( D - C ) ) )

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
    #
    cD
    cc
    wcel
    #
    cC
    cD
    wne
    #
    w3a
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
    cdiv
    co
    #
    @5
    @7
    cdiv
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
    cdiv
    co
    @0
    @5
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    @7
    cc0
    wne
    #
    wa
    @9
    @10
    wceq
    #
    @4
    cA
    cB
    subcl
    @4
    @14
    @15
    @1
    @2
    @14
    @3
    cC
    cD
    subcl
    3adant3
    @1
    @2
    @15
    @3
    @1
    @2
    wa
    @7
    cc0
    cC
    cD
    cC
    cD
    subeq0
    necon3bid
    biimp3ar
    jca
    @13
    @14
    @15
    @16
    @5
    @7
    div2neg
    3expb
    syl2an
    @0
    @4
    @6
    @11
    @8
    @12
    cdiv
    cA
    cB
    negsubdi2
    @1
    @2
    @8
    @12
    wceq
    @3
    cC
    cD
    negsubdi2
    3adant3
    oveqan12d
    eqtr3d
end
