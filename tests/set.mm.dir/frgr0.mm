include "c0.mm"
include "cfrgr.mm"
include "wcel.mm"
include "cusgr.mm"
include "cv.mm"
include "cpr.mm"
include "cedg.mm"
include "cfv.mm"
include "wss.mm"
include "wreu.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "usgr0.mm"
include "ral0.mm"
include "cvtx.mm"
include "vtxval0.mm"
include "eqcomi.mm"
include "eqid.mm"
include "frgrusgrfrcond.mm"
include "mpbir2an.mm"

theorem frgr0
  let vk: setvar k
  let vl: setvar l
  let vx: setvar x


  assert |- (/) e. FriendGraph

  proof
    c0
    cfrgr
    wcel
    c0
    cusgr
    wcel
    vx
    cv
    #
    vk
    cv
    #
    cpr
    @0
    vl
    cv
    cpr
    cpr
    c0
    cedg
    cfv
    #
    wss
    vx
    c0
    wreu
    vl
    c0
    @1
    csn
    cdif
    wral
    #
    vk
    c0
    wral
    usgr0
    @3
    vk
    ral0
    vx
    vk
    @2
    c0
    c0
    vl
    c0
    cvtx
    cfv
    c0
    vtxval0
    eqcomi
    @2
    eqid
    frgrusgrfrcond
    mpbir2an
end
