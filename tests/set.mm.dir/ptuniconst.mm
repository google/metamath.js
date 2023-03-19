include "wcel.mm"
include "ctop.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "ctopon.mm"
include "cfv.mm"
include "cuni.mm"
include "wceq.mm"
include "toptopon.mm"
include "pttoponconst.mm"
include "sylan2b.mm"
include "toponuni.mm"
include "syl.mm"

theorem ptuniconst
  let cA: class A
  let cR: class R
  let cJ: class J
  let cV: class V
  let cX: class X
  let vx: setvar x
  assume ptuniconst.2: |- J = ( Xt_ ` ( A X. { R } ) )
  assume ptuniconst.1: |- X = U. R


  assert |- ( ( A e. V /\ R e. Top ) -> ( X ^m A ) = U. J )

  proof
    cA
    cV
    wcel
    #
    cR
    ctop
    wcel
    #
    wa
    cJ
    cX
    cA
    cmap
    co
    #
    ctopon
    cfv
    wcel
    #
    @2
    cJ
    cuni
    wceq
    @1
    @0
    cR
    cX
    ctopon
    cfv
    wcel
    @3
    cR
    cX
    ptuniconst.1
    toptopon
    cA
    cR
    cJ
    cV
    cX
    ptuniconst.2
    pttoponconst
    sylan2b
    @2
    cJ
    toponuni
    syl
end
