include "ctcl.mm"
include "cfv.mm"
include "cid.mm"
include "cun.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "ccnv.mm"
include "wfun.mm"
include "frege114.mm"
include "frege125.mm"
include "ax-mp.mm"

theorem frege126
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


  assert |- ( Fun `' `' R -> ( Y R X -> ( Y ( t+ ` R ) M -> ( -. X ( t+ ` R ) M -> M ( ( t+ ` R ) u. _I ) X ) ) ) )

  proof
    cX
    cM
    cR
    ctcl
    cfv
    #
    cid
    cun
    #
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
    cY
    cM
    @0
    wbr
    @2
    wi
    wi
    wi
    cR
    cW
    cU
    cM
    cX
    frege124.m
    frege123.x
    frege114
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
    frege125
    ax-mp
end
