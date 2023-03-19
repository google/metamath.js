include "cv.mm"
include "wbr.mm"
include "ctcl.mm"
include "cfv.mm"
include "cid.mm"
include "cun.mm"
include "wi.mm"
include "wal.mm"
include "ccnv.mm"
include "wfun.mm"
include "frege110.mm"
include "frege123.mm"
include "ax-mp.mm"

theorem frege124
  let cR: class R
  let cS: class S
  let cU: class U
  let cM: class M
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  assume frege123.x: |- X e. U
  assume frege123.y: |- Y e. V
  assume frege124.m: |- M e. W
  assume frege124.r: |- R e. S


  assert |- ( Fun `' `' R -> ( Y R X -> ( Y ( t+ ` R ) M -> X ( ( t+ ` R ) u. _I ) M ) ) )

  proof
    cY
    va
    cv
    #
    cR
    wbr
    cX
    @0
    cR
    ctcl
    cfv
    #
    cid
    cun
    #
    wbr
    wi
    va
    wal
    cY
    cM
    @1
    wbr
    cX
    cM
    @2
    wbr
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
    @3
    wi
    wi
    cU
    cV
    cW
    cS
    cR
    cM
    cX
    cY
    va
    frege123.x
    frege123.y
    frege124.m
    frege124.r
    frege110
    cR
    cU
    cM
    cV
    cX
    cY
    va
    frege123.x
    frege123.y
    frege123
    ax-mp
end
