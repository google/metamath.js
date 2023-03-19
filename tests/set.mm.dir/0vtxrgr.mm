include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "crgr.mm"
include "wbr.mm"
include "cxnn0.mm"
include "cvtxdg.mm"
include "wral.mm"
include "simpr.mm"
include "rzal.mm"
include "ad2antlr.mm"
include "wb.mm"
include "eqid.mm"
include "isrgr.mm"
include "adantlr.mm"
include "mpbir2and.mm"
include "ralrimiva.mm"

theorem 0vtxrgr
  let vk: setvar k
  let cG: class G
  let cW: class W
  let vv: setvar v

  disjoint G k
  disjoint W k
  disjoint G v
  disjoint k v
  assert |- ( ( G e. W /\ ( Vtx ` G ) = (/) ) -> A. k e. NN0* G RegGraph k )

  proof
    cG
    cW
    wcel
    #
    cG
    cvtx
    cfv
    #
    c0
    wceq
    #
    wa
    #
    cG
    vk
    cv
    #
    crgr
    wbr
    #
    vk
    cxnn0
    @3
    @4
    cxnn0
    wcel
    #
    wa
    @5
    @6
    vv
    cv
    cG
    cvtxdg
    cfv
    #
    cfv
    @4
    wceq
    #
    vv
    @1
    wral
    #
    @3
    @6
    simpr
    @2
    @9
    @0
    @6
    @8
    vv
    @1
    rzal
    ad2antlr
    @0
    @6
    @5
    @6
    @9
    wa
    wb
    @2
    vv
    @7
    cG
    @4
    @1
    cW
    cxnn0
    @1
    eqid
    @7
    eqid
    isrgr
    adantlr
    mpbir2and
    ralrimiva
end
