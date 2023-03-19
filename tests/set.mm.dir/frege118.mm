include "cv.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "ccnv.mm"
include "wfun.mm"
include "wsbc.mm"
include "frege58c.mm"
include "wcel.mm"
include "wb.mm"
include "sbcimg.mm"
include "ax-mp.mm"
include "csb.mm"
include "sbcbr1g.mm"
include "csbvarg.mm"
include "breq1i.mm"
include "bitri.mm"
include "sbcal.mm"
include "sbcg.mm"
include "imbi12i.mm"
include "albii.mm"
include "sylib.mm"
include "frege117.mm"

theorem frege118
  let cR: class R
  let cU: class U
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  assume frege116.x: |- X e. U
  assume frege118.y: |- Y e. V

  disjoint R a
  disjoint X a
  disjoint Y a
  disjoint a b
  disjoint R b
  disjoint X b
  assert |- ( Fun `' `' R -> ( Y R X -> A. a ( Y R a -> a = X ) ) )

  proof
    vb
    cv
    #
    cX
    cR
    wbr
    #
    @0
    va
    cv
    #
    cR
    wbr
    #
    @2
    cX
    wceq
    #
    wi
    #
    va
    wal
    #
    wi
    #
    vb
    wal
    #
    cY
    cX
    cR
    wbr
    #
    cY
    @2
    cR
    wbr
    #
    @4
    wi
    #
    va
    wal
    #
    wi
    #
    wi
    cR
    ccnv
    ccnv
    wfun
    @13
    wi
    @8
    @7
    vb
    cY
    wsbc
    #
    @13
    @7
    vb
    cY
    cV
    frege118.y
    frege58c
    @14
    @1
    vb
    cY
    wsbc
    #
    @6
    vb
    cY
    wsbc
    #
    wi
    #
    @13
    cY
    cV
    wcel
    #
    @14
    @17
    wb
    frege118.y
    @1
    @6
    vb
    cY
    cV
    sbcimg
    ax-mp
    @15
    @9
    @16
    @12
    @15
    vb
    cY
    @0
    csb
    #
    cX
    cR
    wbr
    #
    @9
    @18
    @15
    @20
    wb
    frege118.y
    vb
    cY
    @0
    cX
    cR
    cV
    sbcbr1g
    ax-mp
    @19
    cY
    cX
    cR
    @18
    @19
    cY
    wceq
    frege118.y
    vb
    cY
    cV
    csbvarg
    ax-mp
    #
    breq1i
    bitri
    @16
    @5
    vb
    cY
    wsbc
    #
    va
    wal
    @12
    @5
    va
    vb
    cY
    sbcal
    @22
    @11
    va
    @22
    @3
    vb
    cY
    wsbc
    #
    @4
    vb
    cY
    wsbc
    #
    wi
    #
    @11
    @18
    @22
    @25
    wb
    frege118.y
    @3
    @4
    vb
    cY
    cV
    sbcimg
    ax-mp
    @23
    @10
    @24
    @4
    @23
    @19
    @2
    cR
    wbr
    #
    @10
    @18
    @23
    @26
    wb
    frege118.y
    vb
    cY
    @0
    @2
    cR
    cV
    sbcbr1g
    ax-mp
    @19
    cY
    @2
    cR
    @21
    breq1i
    bitri
    @18
    @24
    @4
    wb
    frege118.y
    @4
    vb
    cY
    cV
    sbcg
    ax-mp
    imbi12i
    bitri
    albii
    bitri
    imbi12i
    bitri
    sylib
    cR
    cU
    cX
    cY
    va
    vb
    frege116.x
    frege117
    ax-mp
end
