include "ccnv.mm"
include "wfun.mm"
include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "cid.mm"
include "cun.mm"
include "wi.mm"
include "frege127.mm"
include "frege51.mm"
include "ax-mp.mm"

theorem frege128
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


  assert |- ( ( M ( ( t+ ` R ) u. _I ) Y -> ( Y R X -> ( -. X ( t+ ` R ) M -> M ( ( t+ ` R ) u. _I ) X ) ) ) -> ( Fun `' `' R -> ( ( -. Y ( t+ ` R ) M -> M ( ( t+ ` R ) u. _I ) Y ) -> ( Y R X -> ( -. X ( t+ ` R ) M -> M ( ( t+ ` R ) u. _I ) X ) ) ) ) )

  proof
    cR
    ccnv
    ccnv
    wfun
    #
    cY
    cM
    cR
    ctcl
    cfv
    #
    wbr
    #
    cY
    cX
    cR
    wbr
    cX
    cM
    @1
    wbr
    wn
    cM
    cX
    @1
    cid
    cun
    #
    wbr
    wi
    wi
    #
    wi
    wi
    cM
    cY
    @3
    wbr
    #
    @4
    wi
    @0
    @2
    wn
    @5
    wi
    @4
    wi
    wi
    wi
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
    frege127
    @0
    @2
    @4
    @5
    frege51
    ax-mp
end
