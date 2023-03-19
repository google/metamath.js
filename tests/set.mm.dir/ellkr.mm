include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wceq.mm"
include "lkrval.mm"
include "eleq2d.mm"
include "cbs.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "eqid.mm"
include "lflf.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "fvex.mm"
include "elsn.mm"
include "anbi2i.mm"
include "syl6bb.mm"
include "bitrd.mm"

theorem ellkr
  let cD: class D
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lkrfval2.v: |- V = ( Base ` W )
  assume lkrfval2.d: |- D = ( Scalar ` W )
  assume lkrfval2.o: |- .0. = ( 0g ` D )
  assume lkrfval2.f: |- F = ( LFnl ` W )
  assume lkrfval2.k: |- K = ( LKer ` W )


  assert |- ( ( W e. Y /\ G e. F ) -> ( X e. ( K ` G ) <-> ( X e. V /\ ( G ` X ) = .0. ) ) )

  proof
    cW
    cY
    wcel
    cG
    cF
    wcel
    wa
    #
    cX
    cG
    cK
    cfv
    #
    wcel
    cX
    cG
    ccnv
    c.0
    csn
    #
    cima
    #
    wcel
    #
    cX
    cV
    wcel
    #
    cX
    cG
    cfv
    #
    c.0
    wceq
    #
    wa
    #
    @0
    @1
    @3
    cX
    cD
    cF
    cG
    cK
    cW
    cY
    c.0
    lkrfval2.d
    lkrfval2.o
    lkrfval2.f
    lkrfval2.k
    lkrval
    eleq2d
    @0
    @4
    @5
    @6
    @2
    wcel
    #
    wa
    #
    @8
    @0
    cV
    cD
    cbs
    cfv
    #
    cG
    wf
    cG
    cV
    wfn
    @4
    @10
    wb
    cD
    cF
    cG
    @11
    cV
    cW
    cY
    lkrfval2.d
    @11
    eqid
    lkrfval2.v
    lkrfval2.f
    lflf
    cV
    @11
    cG
    ffn
    cV
    cX
    @2
    cG
    elpreima
    3syl
    @9
    @7
    @5
    @6
    c.0
    cX
    cG
    fvex
    elsn
    anbi2i
    syl6bb
    bitrd
end
