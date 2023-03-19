include "cvtx.mm"
include "cfv.mm"
include "chash.mm"
include "c1.mm"
include "wceq.mm"
include "crusgr.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "c0.mm"
include "wral.mm"
include "cusgr.mm"
include "wcel.mm"
include "cxnn0.mm"
include "w3a.mm"
include "cc0.mm"
include "nbgr1vtx.mm"
include "ralrimivw.mm"
include "eqid.mm"
include "rusgrpropnb.mm"
include "anim12i.mm"
include "wi.mm"
include "cvv.mm"
include "fvex.mm"
include "rusgr1vtxlem.mm"
include "ex.mm"
include "mpani.mm"
include "3ad2ant3.mm"
include "com13.mm"
include "impd.mm"
include "adantr.mm"
include "mpd.mm"

theorem rusgr1vtx
  let cG: class G
  let cK: class K
  let vv: setvar v


  assert |- ( ( ( # ` ( Vtx ` G ) ) = 1 /\ G RegUSGraph K ) -> K = 0 )

  proof
    cG
    cvtx
    cfv
    #
    chash
    cfv
    c1
    wceq
    #
    cG
    cK
    crusgr
    wbr
    #
    wa
    cG
    vv
    cv
    #
    cnbgr
    co
    #
    c0
    wceq
    #
    vv
    @0
    wral
    #
    cG
    cusgr
    wcel
    #
    cK
    cxnn0
    wcel
    #
    @4
    chash
    cfv
    cK
    wceq
    vv
    @0
    wral
    #
    w3a
    #
    wa
    #
    cK
    cc0
    wceq
    #
    @1
    @6
    @2
    @10
    @1
    @5
    vv
    @0
    cG
    @3
    nbgr1vtx
    ralrimivw
    vv
    cG
    cK
    @0
    @0
    eqid
    rusgrpropnb
    anim12i
    @1
    @11
    @12
    wi
    @2
    @1
    @6
    @10
    @12
    @10
    @6
    @1
    @12
    @9
    @7
    @6
    @1
    @12
    wi
    #
    wi
    @8
    @9
    @6
    @13
    @9
    @6
    wa
    #
    @0
    cvv
    wcel
    #
    @1
    @12
    cG
    cvtx
    fvex
    @14
    @15
    @1
    wa
    @12
    vv
    @4
    cK
    @0
    cvv
    rusgr1vtxlem
    ex
    mpani
    ex
    3ad2ant3
    com13
    impd
    adantr
    mpd
end
