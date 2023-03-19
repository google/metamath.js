include "wcel.mm"
include "ctopon.mm"
include "cfv.mm"
include "wa.mm"
include "cixp.mm"
include "cmap.mm"
include "co.mm"
include "wral.mm"
include "id.mm"
include "ralrimivw.mm"
include "csn.mm"
include "cxp.mm"
include "cpt.mm"
include "cmpt.mm"
include "fconstmpt.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "pttopon.mm"
include "sylan2.mm"
include "wceq.mm"
include "toponmax.mm"
include "ixpconstg.mm"
include "fveq2d.mm"
include "eleqtrd.mm"

theorem pttoponconst
  let cA: class A
  let cR: class R
  let cJ: class J
  let cV: class V
  let cX: class X
  let vx: setvar x
  assume ptuniconst.2: |- J = ( Xt_ ` ( A X. { R } ) )


  assert |- ( ( A e. V /\ R e. ( TopOn ` X ) ) -> J e. ( TopOn ` ( X ^m A ) ) )

  proof
    cA
    cV
    wcel
    #
    cR
    cX
    ctopon
    cfv
    wcel
    #
    wa
    #
    cJ
    vx
    cA
    cX
    cixp
    #
    ctopon
    cfv
    #
    cX
    cA
    cmap
    co
    #
    ctopon
    cfv
    @1
    @0
    @1
    vx
    cA
    wral
    cJ
    @4
    wcel
    @1
    @1
    vx
    cA
    @1
    id
    ralrimivw
    vx
    cA
    cX
    cJ
    cR
    cV
    cJ
    cA
    cR
    csn
    cxp
    #
    cpt
    cfv
    vx
    cA
    cR
    cmpt
    #
    cpt
    cfv
    ptuniconst.2
    @6
    @7
    cpt
    vx
    cA
    cR
    fconstmpt
    fveq2i
    eqtri
    pttopon
    sylan2
    @2
    @3
    @5
    ctopon
    @1
    @0
    cX
    cR
    wcel
    @3
    @5
    wceq
    cX
    cR
    toponmax
    vx
    cA
    cX
    cV
    cR
    ixpconstg
    sylan2
    fveq2d
    eleqtrd
end
