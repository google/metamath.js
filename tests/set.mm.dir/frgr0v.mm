include "cfrgr.mm"
include "wcel.mm"
include "cusgr.mm"
include "cv.mm"
include "cpr.mm"
include "cedg.mm"
include "cfv.mm"
include "wss.mm"
include "cvtx.mm"
include "wreu.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wa.mm"
include "c0.mm"
include "wceq.mm"
include "ciedg.mm"
include "eqid.mm"
include "frgrusgrfrcond.mm"
include "cuhgr.mm"
include "usgruhgr.mm"
include "adantr.mm"
include "uhgr0vb.mm"
include "syl5ib.mm"
include "simpll.mm"
include "simpr.mm"
include "usgr0e.mm"
include "ral0.mm"
include "wb.mm"
include "raleq.mm"
include "adantl.mm"
include "mpbiri.mm"
include "jca.mm"
include "ex.mm"
include "impbid.mm"
include "syl5bb.mm"

theorem frgr0v
  let cG: class G
  let cW: class W
  let vk: setvar k
  let vl: setvar l
  let vx: setvar x


  assert |- ( ( G e. W /\ ( Vtx ` G ) = (/) ) -> ( G e. FriendGraph <-> ( iEdg ` G ) = (/) ) )

  proof
    cG
    cfrgr
    wcel
    cG
    cusgr
    wcel
    #
    vx
    cv
    #
    vk
    cv
    #
    cpr
    @1
    vl
    cv
    cpr
    cpr
    cG
    cedg
    cfv
    #
    wss
    vx
    cG
    cvtx
    cfv
    #
    wreu
    vl
    @4
    @2
    csn
    cdif
    wral
    #
    vk
    @4
    wral
    #
    wa
    #
    cG
    cW
    wcel
    #
    @4
    c0
    wceq
    #
    wa
    #
    cG
    ciedg
    cfv
    c0
    wceq
    #
    vx
    vk
    @3
    cG
    @4
    vl
    @4
    eqid
    @3
    eqid
    frgrusgrfrcond
    @10
    @7
    @11
    @7
    cG
    cuhgr
    wcel
    #
    @10
    @11
    @0
    @12
    @6
    cG
    usgruhgr
    adantr
    cG
    cW
    uhgr0vb
    syl5ib
    @10
    @11
    @7
    @10
    @11
    wa
    #
    @0
    @6
    @13
    cG
    cW
    @8
    @9
    @11
    simpll
    @10
    @11
    simpr
    usgr0e
    @10
    @6
    @11
    @10
    @6
    @5
    vk
    c0
    wral
    #
    @5
    vk
    ral0
    @9
    @6
    @14
    wb
    @8
    @5
    vk
    @4
    c0
    raleq
    adantl
    mpbiri
    adantr
    jca
    ex
    impbid
    syl5bb
end
