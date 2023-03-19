include "wcel.mm"
include "wa.mm"
include "cedg.mm"
include "cfv.mm"
include "csn.mm"
include "cop.mm"
include "crn.mm"
include "fveq2i.mm"
include "cvv.mm"
include "wceq.mm"
include "snex.mm"
include "a1i.mm"
include "edgopval.mm"
include "sylan2.mm"
include "syl5eq.mm"
include "rnsnopg.mm"
include "adantl.mm"
include "eqtrd.mm"

theorem uspgrloopedg
  let cA: class A
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume uspgrloopvtx.g: |- G = <. V , { <. A , { N } >. } >.


  assert |- ( ( V e. W /\ A e. X ) -> ( Edg ` G ) = { { N } } )

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
    #
    cG
    cedg
    cfv
    #
    cA
    cN
    csn
    #
    cop
    #
    csn
    #
    crn
    #
    @4
    csn
    #
    @2
    @3
    cV
    @6
    cop
    #
    cedg
    cfv
    #
    @7
    cG
    @9
    cedg
    uspgrloopvtx.g
    fveq2i
    @1
    @0
    @6
    cvv
    wcel
    #
    @10
    @7
    wceq
    @11
    @1
    @5
    snex
    a1i
    @6
    cV
    cW
    cvv
    edgopval
    sylan2
    syl5eq
    @1
    @7
    @8
    wceq
    @0
    cA
    @4
    cX
    rnsnopg
    adantl
    eqtrd
end
