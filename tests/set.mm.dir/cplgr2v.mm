include "cuhgr.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "wa.mm"
include "ccplgr.mm"
include "cv.mm"
include "cuvtx.mm"
include "wral.mm"
include "wb.mm"
include "iscplgr.mm"
include "adantr.mm"
include "uvtx2vtx1edgb.mm"
include "bitr4d.mm"

theorem cplgr2v
  let cE: class E
  let cG: class G
  let cV: class V
  let vv: setvar v
  let vn: setvar n
  assume cplgr0v.v: |- V = ( Vtx ` G )
  assume cplgr2v.e: |- E = ( Edg ` G )


  assert |- ( ( G e. UHGraph /\ ( # ` V ) = 2 ) -> ( G e. ComplGraph <-> V e. E ) )

  proof
    cG
    cuhgr
    wcel
    #
    cV
    chash
    cfv
    c2
    wceq
    #
    wa
    cG
    ccplgr
    wcel
    #
    vv
    cv
    cG
    cuvtx
    cfv
    wcel
    vv
    cV
    wral
    #
    cV
    cE
    wcel
    @0
    @2
    @3
    wb
    @1
    vv
    cG
    cV
    cuhgr
    cplgr0v.v
    iscplgr
    adantr
    vv
    cE
    cG
    cV
    cplgr0v.v
    cplgr2v.e
    uvtx2vtx1edgb
    bitr4d
end
