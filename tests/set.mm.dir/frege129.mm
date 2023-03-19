include "ctcl.mm"
include "cfv.mm"
include "cid.mm"
include "cun.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "ccnv.mm"
include "wfun.mm"
include "frege111.mm"
include "frege128.mm"
include "ax-mp.mm"

theorem frege129
  let cR: class R
  let cS: class S
  let cU: class U
  let cM: class M
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume frege123.x: |- X e. U
  assume frege123.y: |- Y e. V
  assume frege124.m: |- M e. W
  assume frege124.r: |- R e. S


  assert |- ( Fun `' `' R -> ( ( -. Y ( t+ ` R ) M -> M ( ( t+ ` R ) u. _I ) Y ) -> ( Y R X -> ( -. X ( t+ ` R ) M -> M ( ( t+ ` R ) u. _I ) X ) ) ) )

  proof
    cM
    cY
    cR
    ctcl
    cfv
    #
    cid
    cun
    #
    wbr
    #
    cY
    cX
    cR
    wbr
    cX
    cM
    @0
    wbr
    wn
    cM
    cX
    @1
    wbr
    wi
    wi
    #
    wi
    cR
    ccnv
    ccnv
    wfun
    cY
    cM
    @0
    wbr
    wn
    @2
    wi
    @3
    wi
    wi
    cW
    cV
    cU
    cS
    cR
    cX
    cY
    cM
    frege124.m
    frege123.y
    frege123.x
    frege124.r
    frege111
    cR
    cS
    cU
    cM
    cV
    cW
    cX
    cY
    frege123.x
    frege123.y
    frege124.m
    frege124.r
    frege128
    ax-mp
end
