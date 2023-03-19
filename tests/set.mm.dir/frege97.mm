include "cv.mm"
include "ctcl.mm"
include "cfv.mm"
include "csn.mm"
include "cima.mm"
include "wcel.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "whe.mm"
include "frege75.mm"
include "cvv.mm"
include "vex.mm"
include "frege96.mm"
include "cop.mm"
include "df-br.mm"
include "elexi.mm"
include "elimasn.mm"
include "bitr4i.mm"
include "imbi2i.mm"
include "3imtr3i.mm"
include "alrimiv.mm"
include "mpg.mm"

theorem frege97
  let cR: class R
  let cU: class U
  let cW: class W
  let cX: class X
  let va: setvar a
  let vb: setvar b
  assume frege97.x: |- X e. U
  assume frege97.r: |- R e. W


  assert |- R hereditary ( ( t+ ` R ) " { X } )

  proof
    vb
    cv
    #
    cR
    ctcl
    cfv
    #
    cX
    csn
    cima
    #
    wcel
    #
    @0
    va
    cv
    #
    cR
    wbr
    #
    @4
    @2
    wcel
    #
    wi
    #
    va
    wal
    wi
    @2
    cR
    whe
    vb
    vb
    va
    @2
    cR
    frege75
    @3
    @7
    va
    cX
    @0
    @1
    wbr
    #
    @5
    cX
    @4
    @1
    wbr
    #
    wi
    @3
    @7
    cW
    cR
    cU
    cvv
    cvv
    cX
    @0
    @4
    frege97.x
    vb
    vex
    #
    va
    vex
    #
    frege97.r
    frege96
    @8
    cX
    @0
    cop
    @1
    wcel
    @3
    cX
    @0
    @1
    df-br
    @1
    cX
    @0
    cX
    cU
    frege97.x
    elexi
    #
    @10
    elimasn
    bitr4i
    @9
    @6
    @5
    @9
    cX
    @4
    cop
    @1
    wcel
    @6
    cX
    @4
    @1
    df-br
    @1
    cX
    @4
    @12
    @11
    elimasn
    bitr4i
    imbi2i
    3imtr3i
    alrimiv
    mpg
end
