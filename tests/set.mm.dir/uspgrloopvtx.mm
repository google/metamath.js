include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "csn.mm"
include "cop.mm"
include "fveq2i.mm"
include "cvv.mm"
include "wceq.mm"
include "snex.mm"
include "opvtxfv.mm"
include "mpan2.mm"
include "syl5eq.mm"

theorem uspgrloopvtx
  let cA: class A
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  assume uspgrloopvtx.g: |- G = <. V , { <. A , { N } >. } >.


  assert |- ( V e. W -> ( Vtx ` G ) = V )

  proof
    cV
    cW
    wcel
    #
    cG
    cvtx
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
    cvtx
    cfv
    #
    cV
    cG
    @3
    cvtx
    uspgrloopvtx.g
    fveq2i
    @0
    @2
    cvv
    wcel
    @4
    cV
    wceq
    @1
    snex
    @2
    cV
    cW
    cvv
    opvtxfv
    mpan2
    syl5eq
end
