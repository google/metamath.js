include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "ctx.mm"
include "co.mm"
include "cxp.mm"
include "ctopon.mm"
include "cfv.mm"
include "cuni.mm"
include "wceq.mm"
include "toptopon.mm"
include "txtopon.mm"
include "syl2anb.mm"
include "toponuni.mm"
include "syl.mm"

theorem txuni
  let cR: class R
  let cS: class S
  let cX: class X
  let cY: class Y
  assume txuni.1: |- X = U. R
  assume txuni.2: |- Y = U. S


  assert |- ( ( R e. Top /\ S e. Top ) -> ( X X. Y ) = U. ( R tX S ) )

  proof
    cR
    ctop
    wcel
    #
    cS
    ctop
    wcel
    #
    wa
    cR
    cS
    ctx
    co
    #
    cX
    cY
    cxp
    #
    ctopon
    cfv
    wcel
    #
    @3
    @2
    cuni
    wceq
    @0
    cR
    cX
    ctopon
    cfv
    wcel
    cS
    cY
    ctopon
    cfv
    wcel
    @4
    @1
    cR
    cX
    txuni.1
    toptopon
    cS
    cY
    txuni.2
    toptopon
    cR
    cS
    cX
    cY
    txtopon
    syl2anb
    @3
    @2
    toponuni
    syl
end
