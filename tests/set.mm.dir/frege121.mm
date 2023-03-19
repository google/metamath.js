include "ccnv.mm"
include "wfun.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "ctcl.mm"
include "cfv.mm"
include "cid.mm"
include "cun.mm"
include "frege120.mm"
include "frege20.mm"
include "ax-mp.mm"

theorem frege121
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


  assert |- ( ( A = X -> X ( ( t+ ` R ) u. _I ) A ) -> ( Fun `' `' R -> ( Y R X -> ( Y R A -> X ( ( t+ ` R ) u. _I ) A ) ) ) )

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
    cA
    cR
    wbr
    #
    cA
    cX
    wceq
    #
    wi
    wi
    wi
    @3
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
    @0
    @1
    @2
    @4
    wi
    wi
    wi
    wi
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
    frege120
    @0
    @1
    @2
    @3
    @4
    frege20
    ax-mp
end
