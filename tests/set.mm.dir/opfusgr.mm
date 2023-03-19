include "cop.mm"
include "cfusgr.mm"
include "wcel.mm"
include "cusgr.mm"
include "cvtx.mm"
include "cfv.mm"
include "cfn.mm"
include "wa.mm"
include "eqid.mm"
include "isfusgr.mm"
include "opvtxfv.mm"
include "eleq1d.mm"
include "anbi2d.mm"
include "syl5bb.mm"

theorem opfusgr
  let cE: class E
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( ( V e. X /\ E e. Y ) -> ( <. V , E >. e. FinUSGraph <-> ( <. V , E >. e. USGraph /\ V e. Fin ) ) )

  proof
    cV
    cE
    cop
    #
    cfusgr
    wcel
    @0
    cusgr
    wcel
    #
    @0
    cvtx
    cfv
    #
    cfn
    wcel
    #
    wa
    cV
    cX
    wcel
    cE
    cY
    wcel
    wa
    #
    @1
    cV
    cfn
    wcel
    #
    wa
    @0
    @2
    @2
    eqid
    isfusgr
    @4
    @3
    @5
    @1
    @4
    @2
    cV
    cfn
    cE
    cV
    cX
    cY
    opvtxfv
    eleq1d
    anbi2d
    syl5bb
end
