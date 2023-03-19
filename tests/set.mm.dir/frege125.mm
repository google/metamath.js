include "ccnv.mm"
include "wfun.mm"
include "wbr.mm"
include "ctcl.mm"
include "cfv.mm"
include "cid.mm"
include "cun.mm"
include "wi.mm"
include "wn.mm"
include "frege124.mm"
include "frege20.mm"
include "ax-mp.mm"

theorem frege125
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


  assert |- ( ( X ( ( t+ ` R ) u. _I ) M -> ( -. X ( t+ ` R ) M -> M ( ( t+ ` R ) u. _I ) X ) ) -> ( Fun `' `' R -> ( Y R X -> ( Y ( t+ ` R ) M -> ( -. X ( t+ ` R ) M -> M ( ( t+ ` R ) u. _I ) X ) ) ) ) )

  proof
    cR
    ccnv
    ccnv
    wfun
    #
    cY
    cX
    cR
    wbr
    #
    cY
    cM
    cR
    ctcl
    cfv
    #
    wbr
    #
    cX
    cM
    @2
    cid
    cun
    #
    wbr
    #
    wi
    wi
    wi
    @5
    cX
    cM
    @2
    wbr
    wn
    cM
    cX
    @4
    wbr
    wi
    #
    wi
    @0
    @1
    @3
    @6
    wi
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
    frege124
    @0
    @1
    @3
    @5
    @6
    frege20
    ax-mp
end
