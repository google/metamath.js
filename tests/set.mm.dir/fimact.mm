include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wfun.mm"
include "wa.mm"
include "cima.mm"
include "cvv.mm"
include "wcel.mm"
include "ctex.mm"
include "imadomg.mm"
include "imp.mm"
include "sylan.mm"
include "simpl.mm"
include "domtr.mm"
include "syl2anc.mm"

theorem fimact
  let cA: class A
  let cF: class F


  assert |- ( ( A ~<_ _om /\ Fun F ) -> ( F " A ) ~<_ _om )

  proof
    cA
    com
    cdom
    wbr
    #
    cF
    wfun
    #
    wa
    cF
    cA
    cima
    #
    cA
    cdom
    wbr
    #
    @0
    @2
    com
    cdom
    wbr
    @0
    cA
    cvv
    wcel
    #
    @1
    @3
    cA
    ctex
    @4
    @1
    @3
    cA
    cvv
    cF
    imadomg
    imp
    sylan
    @0
    @1
    simpl
    @2
    cA
    com
    domtr
    syl2anc
end
