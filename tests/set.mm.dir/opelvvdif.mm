include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "wn.mm"
include "cvv.mm"
include "cxp.mm"
include "cdif.mm"
include "opelvvg.mm"
include "biantrurd.mm"
include "eldif.mm"
include "syl6rbbr.mm"

theorem opelvvdif
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( <. A , B >. e. ( ( _V X. _V ) \ R ) <-> -. <. A , B >. e. R ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
    cA
    cB
    cop
    #
    cR
    wcel
    wn
    #
    @1
    cvv
    cvv
    cxp
    #
    wcel
    #
    @2
    wa
    @1
    @3
    cR
    cdif
    wcel
    @0
    @4
    @2
    cA
    cB
    cV
    cW
    opelvvg
    biantrurd
    @1
    @3
    cR
    eldif
    syl6rbbr
end
