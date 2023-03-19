include "csuc.mm"
include "wcel.mm"
include "com.mm"
include "wceq.mm"
include "wo.mm"
include "csn.mm"
include "cdif.mm"
include "cen.mm"
include "wbr.mm"
include "elsuci.mm"
include "phplem2.mm"
include "wa.mm"
include "enref.mm"
include "word.mm"
include "nnord.mm"
include "orddif.mm"
include "syl.mm"
include "sneq.mm"
include "difeq2d.mm"
include "eqcoms.mm"
include "sylan9eq.mm"
include "syl5breq.mm"
include "jaodan.mm"
include "sylan2.mm"

theorem phplem3
  let cA: class A
  let cB: class B
  let vf: setvar f
  assume phplem2.1: |- A e. _V
  assume phplem2.2: |- B e. _V


  assert |- ( ( A e. _om /\ B e. suc A ) -> A ~~ ( suc A \ { B } ) )

  proof
    cB
    cA
    csuc
    #
    wcel
    cA
    com
    wcel
    #
    cB
    cA
    wcel
    #
    cB
    cA
    wceq
    #
    wo
    cA
    @0
    cB
    csn
    #
    cdif
    #
    cen
    wbr
    #
    cB
    cA
    elsuci
    @1
    @2
    @6
    @3
    cA
    cB
    phplem2.1
    phplem2.2
    phplem2
    @1
    @3
    wa
    cA
    cA
    @5
    cen
    cA
    phplem2.1
    enref
    @1
    @3
    cA
    @0
    cA
    csn
    #
    cdif
    #
    @5
    @1
    cA
    word
    cA
    @8
    wceq
    cA
    nnord
    cA
    orddif
    syl
    @8
    @5
    wceq
    cA
    cB
    cA
    cB
    wceq
    @7
    @4
    @0
    cA
    cB
    sneq
    difeq2d
    eqcoms
    sylan9eq
    syl5breq
    jaodan
    sylan2
end
