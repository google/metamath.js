include "wcel.mm"
include "c0.mm"
include "clinc.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "c0g.mm"
include "csca.mm"
include "cbs.mm"
include "cmap.mm"
include "cpw.mm"
include "wceq.mm"
include "csn.mm"
include "0ex.mm"
include "snid.mm"
include "c1o.mm"
include "cvv.mm"
include "fvex.mm"
include "map0e.mm"
include "mp1i.mm"
include "df1o2.mm"
include "syl6eq.mm"
include "syl5eleqr.mm"
include "0elpw.mm"
include "a1i.mm"
include "lincval.mm"
include "mpd3an23.mm"
include "mpt0.mm"
include "oveq2d.mm"
include "eqid.mm"
include "gsum0.mm"
include "eqtrd.mm"

theorem lincval0
  let cM: class M
  let cX: class X
  let vv: setvar v
  let vk: setvar k
  let vx: setvar x


  assert |- ( M e. X -> ( (/) ( linC ` M ) (/) ) = ( 0g ` M ) )

  proof
    cM
    cX
    wcel
    #
    c0
    c0
    cM
    clinc
    cfv
    co
    #
    cM
    vv
    c0
    vv
    cv
    #
    c0
    cfv
    @2
    cM
    cvsca
    cfv
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cM
    c0g
    cfv
    #
    @0
    c0
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    c0
    cmap
    co
    #
    wcel
    c0
    cM
    cbs
    cfv
    #
    cpw
    wcel
    #
    @1
    @5
    wceq
    @0
    c0
    c0
    csn
    #
    @9
    c0
    0ex
    snid
    @0
    @9
    c1o
    @12
    @8
    cvv
    wcel
    @9
    c1o
    wceq
    @0
    @7
    cbs
    fvex
    @8
    cvv
    map0e
    mp1i
    df1o2
    syl6eq
    syl5eleqr
    @11
    @0
    @10
    0elpw
    a1i
    vv
    c0
    cM
    c0
    cX
    lincval
    mpd3an23
    @0
    @5
    cM
    c0
    cgsu
    co
    @6
    @0
    @4
    c0
    cM
    cgsu
    @4
    c0
    wceq
    @0
    vv
    @3
    mpt0
    a1i
    oveq2d
    cM
    @6
    @6
    eqid
    gsum0
    syl6eq
    eqtrd
end
