include "cvtx.mm"
include "cfv.mm"
include "wcel.mm"
include "cnbgr.mm"
include "co.mm"
include "wnel.mm"
include "wi.mm"
include "cv.mm"
include "wral.mm"
include "wceq.mm"
include "id.mm"
include "oveq2.mm"
include "neleq12d.mm"
include "rspccv.mm"
include "eqid.mm"
include "nbgrnself.mm"
include "a1i.mm"
include "syl11.mm"
include "wn.mm"
include "nbgrisvtxOLD.mm"
include "ex.mm"
include "con3rr3.mm"
include "df-nel.mm"
include "syl6ibr.mm"
include "pm2.61i.mm"

theorem nbgrnself2OLD
  let cG: class G
  let cN: class N
  let cW: class W
  let vv: setvar v


  assert |- ( G e. W -> N e/ ( G NeighbVtx N ) )

  proof
    cN
    cG
    cvtx
    cfv
    #
    wcel
    #
    cG
    cW
    wcel
    #
    cN
    cG
    cN
    cnbgr
    co
    #
    wnel
    #
    wi
    vv
    cv
    #
    cG
    @5
    cnbgr
    co
    #
    wnel
    #
    vv
    @0
    wral
    #
    @1
    @4
    @2
    @7
    @4
    vv
    cN
    @0
    @5
    cN
    wceq
    #
    @5
    cN
    @6
    @3
    @9
    id
    @5
    cN
    cG
    cnbgr
    oveq2
    neleq12d
    rspccv
    @8
    @2
    vv
    cG
    @0
    @0
    eqid
    #
    nbgrnself
    a1i
    syl11
    @1
    wn
    @2
    cN
    @3
    wcel
    #
    wn
    @4
    @2
    @11
    @1
    @2
    @11
    @1
    cG
    cN
    cN
    @0
    cW
    @10
    nbgrisvtxOLD
    ex
    con3rr3
    cN
    @3
    df-nel
    syl6ibr
    pm2.61i
end
