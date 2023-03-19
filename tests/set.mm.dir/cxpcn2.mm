include "crp.mm"
include "cc.mm"
include "cv.mm"
include "ccxp.mm"
include "co.mm"
include "cmpt2.mm"
include "ctx.mm"
include "ccn.mm"
include "wcel.mm"
include "wtru.mm"
include "cmnf.mm"
include "cc0.mm"
include "cioc.mm"
include "cdif.mm"
include "crest.mm"
include "ctopon.mm"
include "cfv.mm"
include "wss.mm"
include "cvv.mm"
include "wceq.mm"
include "cnfldtopon.mm"
include "cr.mm"
include "wi.mm"
include "rpcn.mm"
include "ax-1.mm"
include "eqid.mm"
include "ellogdm.mm"
include "sylanbrc.mm"
include "ssriv.mm"
include "cnex.mm"
include "difss.mm"
include "ssexi.mm"
include "restabs.mm"
include "mp3an.mm"
include "eqtr4i.mm"
include "a1i.mm"
include "resttopon.mm"
include "sylancl.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "ssid.mm"
include "cxpcn.mm"
include "cnmpt2res.mm"
include "trud.mm"

theorem cxpcn2
  let vx: setvar x
  let vy: setvar y
  let cJ: class J
  let cK: class K
  assume cxpcn2.j: |- J = ( TopOpen ` CCfld )
  assume cxpcn2.k: |- K = ( J |`t RR+ )

  disjoint x y
  disjoint J x
  disjoint J y
  assert |- ( x e. RR+ , y e. CC |-> ( x ^c y ) ) e. ( ( K tX J ) Cn J )

  proof
    vx
    vy
    crp
    cc
    vx
    cv
    #
    vy
    cv
    ccxp
    co
    #
    cmpt2
    cK
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    wtru
    vx
    vy
    @1
    cJ
    cc
    cmnf
    cc0
    cioc
    co
    #
    cdif
    #
    crest
    co
    #
    cK
    cJ
    cJ
    cJ
    cc
    @3
    crp
    cc
    cK
    cJ
    crp
    crest
    co
    #
    @4
    crp
    crest
    co
    #
    cxpcn2.k
    cJ
    cc
    ctopon
    cfv
    #
    wcel
    #
    crp
    @3
    wss
    #
    @3
    cvv
    wcel
    @6
    @5
    wceq
    cJ
    cxpcn2.j
    cnfldtopon
    #
    vx
    crp
    @3
    @0
    crp
    wcel
    #
    @0
    cc
    wcel
    @0
    cr
    wcel
    #
    @11
    wi
    @0
    @3
    wcel
    @0
    rpcn
    @11
    @12
    ax-1
    @0
    @3
    @3
    eqid
    #
    ellogdm
    sylanbrc
    ssriv
    #
    @3
    cc
    cnex
    cc
    @2
    difss
    #
    ssexi
    crp
    @3
    cJ
    @7
    cvv
    restabs
    mp3an
    eqtr4i
    wtru
    @8
    @3
    cc
    wss
    @4
    @3
    ctopon
    cfv
    wcel
    @8
    wtru
    @10
    a1i
    #
    @15
    @3
    cJ
    cc
    resttopon
    sylancl
    @9
    wtru
    @14
    a1i
    cJ
    cc
    crest
    co
    #
    cJ
    @8
    @17
    cJ
    wceq
    @10
    cJ
    @7
    cc
    cc
    cJ
    @10
    toponunii
    restid
    ax-mp
    eqcomi
    @16
    cc
    cc
    wss
    wtru
    cc
    ssid
    a1i
    vx
    vy
    @3
    cc
    @1
    cmpt2
    @4
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    wtru
    vx
    vy
    @3
    cJ
    @4
    @13
    cxpcn2.j
    @4
    eqid
    cxpcn
    a1i
    cnmpt2res
    trud
end
