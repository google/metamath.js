include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "ctcl.mm"
include "cfv.mm"
include "wi.mm"
include "wsbc.mm"
include "cvv.mm"
include "vex.mm"
include "frege91.mm"
include "sbcth.mm"
include "frege53c.mm"
include "syl.mm"
include "sbcim1.mm"
include "imim2i.mm"
include "wb.mm"
include "csb.mm"
include "sbcbr1g.mm"
include "csbvarg.mm"
include "breq1d.mm"
include "bitrd.mm"
include "ax-mp.mm"
include "dfsbcq.mm"
include "syl5rbbr.mm"
include "eqcom.mm"
include "biimpi.mm"
include "syl6eqel.mm"
include "imbi12d.mm"
include "mpbidi.mm"
include "mp2b.mm"

theorem frege92
  let cR: class R
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vw: setvar w
  assume frege91.x: |- X e. U
  assume frege91.y: |- Y e. V
  assume frege91.r: |- R e. W


  assert |- ( X = Z -> ( X R Y -> Z ( t+ ` R ) Y ) )

  proof
    cX
    cU
    wcel
    #
    cX
    cZ
    wceq
    #
    vw
    cv
    #
    cY
    cR
    wbr
    #
    @2
    cY
    cR
    ctcl
    cfv
    #
    wbr
    #
    wi
    #
    vw
    cZ
    wsbc
    #
    wi
    #
    @1
    cX
    cY
    cR
    wbr
    #
    cZ
    cY
    @4
    wbr
    #
    wi
    #
    wi
    frege91.x
    @0
    @6
    vw
    cX
    wsbc
    @8
    @6
    vw
    cX
    cU
    cR
    cvv
    cV
    cW
    @2
    cY
    vw
    vex
    frege91.y
    frege91.r
    frege91
    sbcth
    @6
    vw
    cX
    cZ
    frege53c
    syl
    @1
    @3
    vw
    cZ
    wsbc
    #
    @5
    vw
    cZ
    wsbc
    #
    wi
    #
    @11
    @8
    @7
    @14
    @1
    @3
    @5
    vw
    cZ
    sbcim1
    imim2i
    @1
    @12
    @9
    @13
    @10
    @9
    @3
    vw
    cX
    wsbc
    #
    @1
    @12
    @0
    @15
    @9
    wb
    frege91.x
    @0
    @15
    vw
    cX
    @2
    csb
    #
    cY
    cR
    wbr
    @9
    vw
    cX
    @2
    cY
    cR
    cU
    sbcbr1g
    @0
    @16
    cX
    cY
    cR
    vw
    cX
    cU
    csbvarg
    breq1d
    bitrd
    ax-mp
    @3
    vw
    cX
    cZ
    dfsbcq
    syl5rbbr
    @1
    cZ
    cU
    wcel
    #
    @13
    @10
    wb
    @1
    cZ
    cX
    cU
    @1
    cZ
    cX
    wceq
    cX
    cZ
    eqcom
    biimpi
    frege91.x
    syl6eqel
    @17
    @13
    vw
    cZ
    @2
    csb
    #
    cY
    @4
    wbr
    @10
    vw
    cZ
    @2
    cY
    @4
    cU
    sbcbr1g
    @17
    @18
    cZ
    cY
    @4
    vw
    cZ
    cU
    csbvarg
    breq1d
    bitrd
    syl
    imbi12d
    mpbidi
    mp2b
end
