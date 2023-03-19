include "cv.mm"
include "ctcl.mm"
include "cfv.mm"
include "cid.mm"
include "cun.mm"
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
include "frege108.mm"
include "cop.mm"
include "df-br.mm"
include "elexi.mm"
include "elimasn.mm"
include "bitr4i.mm"
include "imbi2i.mm"
include "3imtr3i.mm"
include "alrimiv.mm"
include "mpg.mm"

theorem frege109
  let cR: class R
  let cU: class U
  let cV: class V
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  assume frege109.x: |- X e. U
  assume frege109.r: |- R e. V


  assert |- R hereditary ( ( ( t+ ` R ) u. _I ) " { X } )

  proof
    vy
    cv
    #
    cR
    ctcl
    cfv
    cid
    cun
    #
    cX
    csn
    cima
    #
    wcel
    #
    @0
    vz
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
    vz
    wal
    wi
    @2
    cR
    whe
    vy
    vy
    vz
    @2
    cR
    frege75
    @3
    @7
    vz
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
    cU
    cvv
    cvv
    cV
    cR
    @4
    @0
    cX
    frege109.x
    vy
    vex
    #
    vz
    vex
    #
    frege109.r
    frege108
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
    frege109.x
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
