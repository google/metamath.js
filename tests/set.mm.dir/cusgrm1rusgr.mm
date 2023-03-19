include "cfusgr.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "ccusgr.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "crusgr.mm"
include "wbr.mm"
include "cfn.mm"
include "simpr.mm"
include "fusgrvtxfi.mm"
include "adantr.mm"
include "cusgrrusgr.mm"
include "syl3anc.mm"
include "ex.mm"
include "cv.mm"
include "cvtxdg.mm"
include "wceq.mm"
include "wral.mm"
include "cusgr.mm"
include "cxnn0.mm"
include "eqid.mm"
include "rusgrprop0.mm"
include "simp3d.mm"
include "wi.mm"
include "vdiscusgr.mm"
include "syl5.mm"
include "impbid.mm"

theorem cusgrm1rusgr
  let cG: class G
  let cV: class V
  let vv: setvar v
  assume cusgrrusgr.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. FinUSGraph /\ V =/= (/) ) -> ( G e. ComplUSGraph <-> G RegUSGraph ( ( # ` V ) - 1 ) ) )

  proof
    cG
    cfusgr
    wcel
    #
    cV
    c0
    wne
    #
    wa
    #
    cG
    ccusgr
    wcel
    #
    cG
    cV
    chash
    cfv
    c1
    cmin
    co
    #
    crusgr
    wbr
    #
    @2
    @3
    @5
    @2
    @3
    wa
    @3
    cV
    cfn
    wcel
    #
    @1
    @5
    @2
    @3
    simpr
    @2
    @6
    @3
    @0
    @6
    @1
    cG
    cV
    cusgrrusgr.v
    fusgrvtxfi
    adantr
    adantr
    @2
    @1
    @3
    @0
    @1
    simpr
    adantr
    cG
    cV
    cusgrrusgr.v
    cusgrrusgr
    syl3anc
    ex
    @5
    vv
    cv
    cG
    cvtxdg
    cfv
    #
    cfv
    @4
    wceq
    vv
    cV
    wral
    #
    @2
    @3
    @5
    cG
    cusgr
    wcel
    @4
    cxnn0
    wcel
    @8
    vv
    @7
    cG
    @4
    cV
    cusgrrusgr.v
    @7
    eqid
    rusgrprop0
    simp3d
    @0
    @8
    @3
    wi
    @1
    vv
    cG
    cV
    cusgrrusgr.v
    vdiscusgr
    adantr
    syl5
    impbid
end
