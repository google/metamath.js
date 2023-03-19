include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "wne.mm"
include "nbgrisvtx.mm"
include "wceq.mm"
include "wn.mm"
include "wnel.mm"
include "nbgrnself2.mm"
include "df-nel.mm"
include "neleq1.mm"
include "syl5bbr.mm"
include "mpbiri.mm"
include "necon2ai.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "ssriv.mm"

theorem nbgrssovtx
  let cG: class G
  let cV: class V
  let cX: class X
  let vv: setvar v
  assume nbgrssovtx.v: |- V = ( Vtx ` G )


  assert |- ( G NeighbVtx X ) C_ ( V \ { X } )

  proof
    vv
    cG
    cX
    cnbgr
    co
    #
    cV
    cX
    csn
    cdif
    #
    vv
    cv
    #
    @0
    wcel
    #
    @2
    cV
    wcel
    @2
    cX
    wne
    @2
    @1
    wcel
    cG
    cX
    @2
    cV
    nbgrssovtx.v
    nbgrisvtx
    @3
    @2
    cX
    @2
    cX
    wceq
    #
    @3
    wn
    #
    cX
    @0
    wnel
    #
    cG
    cX
    nbgrnself2
    @5
    @2
    @0
    wnel
    @4
    @6
    @2
    @0
    df-nel
    @2
    cX
    @0
    neleq1
    syl5bbr
    mpbiri
    necon2ai
    @2
    cV
    cX
    eldifsn
    sylanbrc
    ssriv
end
