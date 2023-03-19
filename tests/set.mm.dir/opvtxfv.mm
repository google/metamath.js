include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cvtx.mm"
include "cfv.mm"
include "c1st.mm"
include "cvv.mm"
include "cxp.mm"
include "wceq.mm"
include "opelvvg.mm"
include "opvtxval.mm"
include "syl.mm"
include "op1stg.mm"
include "eqtrd.mm"

theorem opvtxfv
  let cE: class E
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( ( V e. X /\ E e. Y ) -> ( Vtx ` <. V , E >. ) = V )

  proof
    cV
    cX
    wcel
    cE
    cY
    wcel
    wa
    #
    cV
    cE
    cop
    #
    cvtx
    cfv
    #
    @1
    c1st
    cfv
    #
    cV
    @0
    @1
    cvv
    cvv
    cxp
    wcel
    @2
    @3
    wceq
    cV
    cE
    cX
    cY
    opelvvg
    @1
    opvtxval
    syl
    cV
    cE
    cX
    cY
    op1stg
    eqtrd
end
