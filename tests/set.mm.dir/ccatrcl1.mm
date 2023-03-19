include "cword.mm"
include "wcel.mm"
include "cconcat.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "eleq1.mm"
include "cvv.mm"
include "wb.mm"
include "wrdv.mm"
include "ccatalpha.mm"
include "syl2an.mm"
include "sylan9bbr.mm"
include "simpl.mm"
include "syl6bi.mm"
include "expimpd.mm"
include "3impia.mm"

theorem ccatrcl1
  let cA: class A
  let cB: class B
  let cS: class S
  let cW: class W
  let cX: class X
  let cY: class Y


  assert |- ( ( A e. Word X /\ B e. Word Y /\ ( W = ( A ++ B ) /\ W e. Word S ) ) -> A e. Word S )

  proof
    cA
    cX
    cword
    wcel
    #
    cB
    cY
    cword
    wcel
    #
    cW
    cA
    cB
    cconcat
    co
    #
    wceq
    #
    cW
    cS
    cword
    #
    wcel
    #
    wa
    cA
    @4
    wcel
    #
    @0
    @1
    wa
    #
    @3
    @5
    @6
    @7
    @3
    wa
    @5
    @6
    cB
    @4
    wcel
    #
    wa
    #
    @6
    @3
    @5
    @2
    @4
    wcel
    #
    @7
    @9
    cW
    @2
    @4
    eleq1
    @0
    cA
    cvv
    cword
    #
    wcel
    cB
    @11
    wcel
    @10
    @9
    wb
    @1
    cX
    cA
    wrdv
    cY
    cB
    wrdv
    cA
    cB
    cS
    ccatalpha
    syl2an
    sylan9bbr
    @6
    @8
    simpl
    syl6bi
    expimpd
    3impia
end
