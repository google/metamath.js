include "wcel.mm"
include "wa.mm"
include "ciedg.mm"
include "cfv.mm"
include "csn.mm"
include "cop.mm"
include "fveq2i.mm"
include "cvv.mm"
include "wceq.mm"
include "snex.mm"
include "a1i.mm"
include "opiedgfv.mm"
include "sylan2.mm"
include "syl5eq.mm"

theorem uspgrloopiedg
  let cA: class A
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume uspgrloopvtx.g: |- G = <. V , { <. A , { N } >. } >.


  assert |- ( ( V e. W /\ A e. X ) -> ( iEdg ` G ) = { <. A , { N } >. } )

  proof
    cV
    cW
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    cG
    ciedg
    cfv
    cV
    cA
    cN
    csn
    cop
    #
    csn
    #
    cop
    #
    ciedg
    cfv
    #
    @3
    cG
    @4
    ciedg
    uspgrloopvtx.g
    fveq2i
    @1
    @0
    @3
    cvv
    wcel
    #
    @5
    @3
    wceq
    @6
    @1
    @2
    snex
    a1i
    @3
    cV
    cW
    cvv
    opiedgfv
    sylan2
    syl5eq
end
