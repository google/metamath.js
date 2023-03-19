include "wfn.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "wceq.mm"
include "elpreima.mm"
include "fvex.mm"
include "elsn.mm"
include "anbi2i.mm"
include "syl6bb.mm"

theorem fniniseg
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( F Fn A -> ( C e. ( `' F " { B } ) <-> ( C e. A /\ ( F ` C ) = B ) ) )

  proof
    cF
    cA
    wfn
    cC
    cF
    ccnv
    cB
    csn
    #
    cima
    wcel
    cC
    cA
    wcel
    #
    cC
    cF
    cfv
    #
    @0
    wcel
    #
    wa
    @1
    @2
    cB
    wceq
    #
    wa
    cA
    cC
    @0
    cF
    elpreima
    @3
    @4
    @1
    @2
    cB
    cC
    cF
    fvex
    elsn
    anbi2i
    syl6bb
end
