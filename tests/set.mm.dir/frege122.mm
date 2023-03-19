include "wceq.mm"
include "ctcl.mm"
include "cfv.mm"
include "cid.mm"
include "cun.mm"
include "wbr.mm"
include "wi.mm"
include "ccnv.mm"
include "wfun.mm"
include "frege112.mm"
include "frege121.mm"
include "ax-mp.mm"

theorem frege122
  let cA: class A
  let cR: class R
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume frege116.x: |- X e. U
  assume frege118.y: |- Y e. V
  assume frege120.a: |- A e. W


  assert |- ( Fun `' `' R -> ( Y R X -> ( Y R A -> X ( ( t+ ` R ) u. _I ) A ) ) )

  proof
    cA
    cX
    wceq
    cX
    cA
    cR
    ctcl
    cfv
    cid
    cun
    wbr
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
    cA
    cR
    wbr
    @0
    wi
    wi
    wi
    cR
    cW
    cX
    cA
    frege120.a
    frege112
    cA
    cR
    cU
    cV
    cW
    cX
    cY
    frege116.x
    frege118.y
    frege120.a
    frege121
    ax-mp
end
