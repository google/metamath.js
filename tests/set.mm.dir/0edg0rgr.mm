include "wcel.mm"
include "ciedg.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "crgr.mm"
include "wbr.mm"
include "cxnn0.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cvtx.mm"
include "wral.mm"
include "simpr.mm"
include "simplr.mm"
include "eqid.mm"
include "vtxdg0e.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "0xnn0.mm"
include "jctil.mm"
include "wb.mm"
include "a1i.mm"
include "isrgr.mm"
include "sylan2.mm"
include "mpbird.mm"

theorem 0edg0rgr
  let cG: class G
  let cW: class W
  let vv: setvar v


  assert |- ( ( G e. W /\ ( iEdg ` G ) = (/) ) -> G RegGraph 0 )

  proof
    cG
    cW
    wcel
    #
    cG
    ciedg
    cfv
    #
    c0
    wceq
    #
    wa
    #
    cG
    cc0
    crgr
    wbr
    #
    cc0
    cxnn0
    wcel
    #
    vv
    cv
    #
    cG
    cvtxdg
    cfv
    #
    cfv
    cc0
    wceq
    #
    vv
    cG
    cvtx
    cfv
    #
    wral
    #
    wa
    #
    @3
    @10
    @5
    @3
    @8
    vv
    @9
    @3
    @6
    @9
    wcel
    #
    wa
    @12
    @2
    @8
    @3
    @12
    simpr
    @0
    @2
    @12
    simplr
    @6
    cG
    @1
    @9
    @9
    eqid
    #
    @1
    eqid
    vtxdg0e
    syl2anc
    ralrimiva
    0xnn0
    jctil
    @2
    @0
    @5
    @4
    @11
    wb
    @5
    @2
    0xnn0
    a1i
    vv
    @7
    cG
    cc0
    @9
    cW
    cxnn0
    @13
    @7
    eqid
    isrgr
    sylan2
    mpbird
end
