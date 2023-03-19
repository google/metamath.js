include "cv.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "ccnv.mm"
include "wfun.mm"
include "wsbc.mm"
include "frege58c.mm"
include "sbcim1.mm"
include "csb.mm"
include "wcel.mm"
include "wb.mm"
include "sbcbr2g.mm"
include "ax-mp.mm"
include "csbvarg.mm"
include "breq2i.mm"
include "bitri.mm"
include "sbceq1g.mm"
include "eqeq1i.mm"
include "3imtr3g.mm"
include "syl.mm"
include "frege119.mm"

theorem frege120
  let cA: class A
  let cR: class R
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  assume frege116.x: |- X e. U
  assume frege118.y: |- Y e. V
  assume frege120.a: |- A e. W


  assert |- ( Fun `' `' R -> ( Y R X -> ( Y R A -> A = X ) ) )

  proof
    cY
    va
    cv
    #
    cR
    wbr
    #
    @0
    cX
    wceq
    #
    wi
    #
    va
    wal
    #
    cY
    cA
    cR
    wbr
    #
    cA
    cX
    wceq
    #
    wi
    #
    wi
    cR
    ccnv
    ccnv
    wfun
    cY
    cX
    cR
    wbr
    @7
    wi
    wi
    @4
    @3
    va
    cA
    wsbc
    #
    @7
    @3
    va
    cA
    cW
    frege120.a
    frege58c
    @8
    @1
    va
    cA
    wsbc
    #
    @2
    va
    cA
    wsbc
    #
    @5
    @6
    @1
    @2
    va
    cA
    sbcim1
    @9
    cY
    va
    cA
    @0
    csb
    #
    cR
    wbr
    #
    @5
    cA
    cW
    wcel
    #
    @9
    @12
    wb
    frege120.a
    va
    cA
    cY
    @0
    cR
    cW
    sbcbr2g
    ax-mp
    @11
    cA
    cY
    cR
    @13
    @11
    cA
    wceq
    frege120.a
    va
    cA
    cW
    csbvarg
    ax-mp
    #
    breq2i
    bitri
    @10
    @11
    cX
    wceq
    #
    @6
    @13
    @10
    @15
    wb
    frege120.a
    va
    cA
    @0
    cX
    cW
    sbceq1g
    ax-mp
    @11
    cA
    cX
    @14
    eqeq1i
    bitri
    3imtr3g
    syl
    cA
    cR
    cU
    cV
    cX
    cY
    va
    frege116.x
    frege118.y
    frege119
    ax-mp
end
