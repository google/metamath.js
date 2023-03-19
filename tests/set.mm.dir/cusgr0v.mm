include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "ciedg.mm"
include "cfv.mm"
include "w3a.mm"
include "cusgr.mm"
include "ccplgr.mm"
include "ccusgr.mm"
include "cvtx.mm"
include "eqeq1i.mm"
include "usgr0v.mm"
include "syl3an2b.mm"
include "cplgr0v.mm"
include "3adant3.mm"
include "iscusgr.mm"
include "sylanbrc.mm"

theorem cusgr0v
  let cG: class G
  let cV: class V
  let cW: class W
  let vv: setvar v
  assume cplgr0v.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. W /\ V = (/) /\ ( iEdg ` G ) = (/) ) -> G e. ComplUSGraph )

  proof
    cG
    cW
    wcel
    #
    cV
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
    cG
    cusgr
    wcel
    #
    cG
    ccplgr
    wcel
    #
    cG
    ccusgr
    wcel
    @1
    @0
    cG
    cvtx
    cfv
    #
    c0
    wceq
    @2
    @3
    cV
    @5
    c0
    cplgr0v.v
    eqeq1i
    cG
    cW
    usgr0v
    syl3an2b
    @0
    @1
    @4
    @2
    cG
    cV
    cW
    cplgr0v.v
    cplgr0v
    3adant3
    cG
    iscusgr
    sylanbrc
end
