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
include "eqid.mm"
include "frgrusgrfrcond.mm"
include "simplbi.mm"

theorem frgrusgr
  let cG: class G
  let vk: setvar k
  let vl: setvar l
  let vx: setvar x


  assert |- ( G e. FriendGraph -> G e. USGraph )

  proof
    cG
    cfrgr
    wcel
    cG
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
    @3
    @1
    csn
    cdif
    wral
    vk
    @3
    wral
    vx
    vk
    @2
    cG
    @3
    vl
    @3
    eqid
    @2
    eqid
    frgrusgrfrcond
    simplbi
end
