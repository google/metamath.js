include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "ciedg.mm"
include "c0.mm"
include "wa.mm"
include "cusgr.mm"
include "wcel.mm"
include "ccplgr.mm"
include "ccusgr.mm"
include "cvv.mm"
include "cplgr1vlem.mm"
include "adantr.mm"
include "simpr.mm"
include "usgr0e.mm"
include "cplgr1v.mm"
include "iscusgr.mm"
include "sylanbrc.mm"

theorem cusgr1v
  let cG: class G
  let cV: class V
  let vv: setvar v
  let vn: setvar n
  assume cplgr0v.v: |- V = ( Vtx ` G )


  assert |- ( ( ( # ` V ) = 1 /\ ( iEdg ` G ) = (/) ) -> G e. ComplUSGraph )

  proof
    cV
    chash
    cfv
    c1
    wceq
    #
    cG
    ciedg
    cfv
    c0
    wceq
    #
    wa
    #
    cG
    cusgr
    wcel
    cG
    ccplgr
    wcel
    #
    cG
    ccusgr
    wcel
    @2
    cG
    cvv
    @0
    cG
    cvv
    wcel
    @1
    cG
    cV
    cplgr0v.v
    cplgr1vlem
    adantr
    @0
    @1
    simpr
    usgr0e
    @0
    @3
    @1
    cG
    cV
    cplgr0v.v
    cplgr1v
    adantr
    cG
    iscusgr
    sylanbrc
end
