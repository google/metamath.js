include "cv.mm"
include "wbr.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "ccnv.mm"
include "wfun.mm"
include "wb.mm"
include "wceq.mm"
include "dffrege115.mm"
include "wsbc.mm"
include "frege68c.mm"
include "sbcal.mm"
include "wcel.mm"
include "sbcimg.mm"
include "ax-mp.mm"
include "csb.mm"
include "sbcbr2g.mm"
include "csbvarg.mm"
include "breq2i.mm"
include "bitri.mm"
include "sbcg.mm"
include "sbceq2g.mm"
include "eqeq2i.mm"
include "imbi12i.mm"
include "albii.mm"
include "syl6ib.mm"

theorem frege116
  let cR: class R
  let cU: class U
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume frege116.x: |- X e. U

  disjoint a b
  disjoint R a
  disjoint R b
  disjoint X a
  disjoint X b
  disjoint a c
  disjoint b c
  disjoint R c
  assert |- ( Fun `' `' R -> A. b ( b R X -> A. a ( b R a -> a = X ) ) )

  proof
    vb
    cv
    #
    vc
    cv
    #
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
    va
    vc
    weq
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
    vc
    wal
    cR
    ccnv
    ccnv
    wfun
    #
    wb
    #
    @10
    @0
    cX
    cR
    wbr
    #
    @4
    @3
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
    wi
    cR
    va
    vb
    vc
    dffrege115
    @11
    @10
    @9
    vc
    cX
    wsbc
    #
    @17
    @9
    @10
    vc
    cX
    cU
    frege116.x
    frege68c
    @18
    @8
    vc
    cX
    wsbc
    #
    vb
    wal
    @17
    @8
    vb
    vc
    cX
    sbcal
    @19
    @16
    vb
    @19
    @2
    vc
    cX
    wsbc
    #
    @7
    vc
    cX
    wsbc
    #
    wi
    #
    @16
    cX
    cU
    wcel
    #
    @19
    @22
    wb
    frege116.x
    @2
    @7
    vc
    cX
    cU
    sbcimg
    ax-mp
    @20
    @12
    @21
    @15
    @20
    @0
    vc
    cX
    @1
    csb
    #
    cR
    wbr
    #
    @12
    @23
    @20
    @25
    wb
    frege116.x
    vc
    cX
    @0
    @1
    cR
    cU
    sbcbr2g
    ax-mp
    @24
    cX
    @0
    cR
    @23
    @24
    cX
    wceq
    frege116.x
    vc
    cX
    cU
    csbvarg
    ax-mp
    #
    breq2i
    bitri
    @21
    @6
    vc
    cX
    wsbc
    #
    va
    wal
    @15
    @6
    va
    vc
    cX
    sbcal
    @27
    @14
    va
    @27
    @4
    vc
    cX
    wsbc
    #
    @5
    vc
    cX
    wsbc
    #
    wi
    #
    @14
    @23
    @27
    @30
    wb
    frege116.x
    @4
    @5
    vc
    cX
    cU
    sbcimg
    ax-mp
    @28
    @4
    @29
    @13
    @23
    @28
    @4
    wb
    frege116.x
    @4
    vc
    cX
    cU
    sbcg
    ax-mp
    @29
    @3
    @24
    wceq
    #
    @13
    @23
    @29
    @31
    wb
    frege116.x
    vc
    cX
    @3
    @1
    cU
    sbceq2g
    ax-mp
    @24
    cX
    @3
    @26
    eqeq2i
    bitri
    imbi12i
    bitri
    albii
    bitri
    imbi12i
    bitri
    albii
    bitri
    syl6ib
    ax-mp
end
