include "cvtx.mm"
include "cfv.mm"
include "wcel.mm"
include "cnbgr.mm"
include "co.mm"
include "wnel.mm"
include "cv.mm"
include "wceq.mm"
include "id.mm"
include "oveq2.mm"
include "neleq12d.mm"
include "eqid.mm"
include "nbgrnself.mm"
include "vtoclri.mm"
include "wn.mm"
include "nbgrisvtx.mm"
include "con3i.mm"
include "df-nel.mm"
include "sylibr.mm"
include "pm2.61i.mm"

theorem nbgrnself2
  let cG: class G
  let cX: class X
  let vv: setvar v


  assert |- X e/ ( G NeighbVtx X )

  proof
    cX
    cG
    cvtx
    cfv
    #
    wcel
    #
    cX
    cG
    cX
    cnbgr
    co
    #
    wnel
    #
    vv
    cv
    #
    cG
    @4
    cnbgr
    co
    #
    wnel
    @3
    vv
    cX
    @0
    @4
    cX
    wceq
    #
    @4
    cX
    @5
    @2
    @6
    id
    @4
    cX
    cG
    cnbgr
    oveq2
    neleq12d
    vv
    cG
    @0
    @0
    eqid
    #
    nbgrnself
    vtoclri
    @1
    wn
    cX
    @2
    wcel
    #
    wn
    @3
    @8
    @1
    cG
    cX
    cX
    @0
    @7
    nbgrisvtx
    con3i
    cX
    @2
    df-nel
    sylibr
    pm2.61i
end
