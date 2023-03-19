include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "ciedg.mm"
include "w3a.mm"
include "cv.mm"
include "crusgr.mm"
include "wbr.mm"
include "cxnn0.mm"
include "wa.mm"
include "cusgr.mm"
include "crgr.mm"
include "usgr0v.mm"
include "adantr.mm"
include "wi.mm"
include "wral.mm"
include "0vtxrgr.mm"
include "breq2.mm"
include "rspccva.mm"
include "ex.mm"
include "syl.mm"
include "3adant3.mm"
include "imp.mm"
include "wb.mm"
include "isrusgr.mm"
include "3ad2antl1.mm"
include "mpbir2and.mm"
include "ralrimiva.mm"

theorem 0vtxrusgr
  let vk: setvar k
  let cG: class G
  let cW: class W
  let vv: setvar v

  disjoint G k
  disjoint W k
  disjoint G v
  disjoint k v
  disjoint W v
  assert |- ( ( G e. W /\ ( Vtx ` G ) = (/) /\ ( iEdg ` G ) = (/) ) -> A. k e. NN0* G RegUSGraph k )

  proof
    cG
    cW
    wcel
    #
    cG
    cvtx
    cfv
    c0
    wceq
    #
    cG
    ciedg
    cfv
    c0
    wceq
    #
    w3a
    #
    cG
    vk
    cv
    #
    crusgr
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
    cG
    cusgr
    wcel
    #
    cG
    @4
    crgr
    wbr
    #
    @3
    @7
    @6
    cG
    cW
    usgr0v
    adantr
    @3
    @6
    @8
    @0
    @1
    @6
    @8
    wi
    #
    @2
    @0
    @1
    wa
    cG
    vv
    cv
    #
    crgr
    wbr
    #
    vv
    cxnn0
    wral
    #
    @9
    vv
    cG
    cW
    0vtxrgr
    @12
    @6
    @8
    @11
    @8
    vv
    @4
    cxnn0
    @10
    @4
    cG
    crgr
    breq2
    rspccva
    ex
    syl
    3adant3
    imp
    @0
    @1
    @6
    @5
    @7
    @8
    wa
    wb
    @2
    cG
    @4
    cW
    cxnn0
    isrusgr
    3ad2antl1
    mpbir2and
    ralrimiva
end
