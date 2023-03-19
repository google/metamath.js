include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "c0.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "c1o.mm"
include "cmat.mm"
include "csn.mm"
include "wceq.mm"
include "0xp.mm"
include "a1i.mm"
include "oveq2d.mm"
include "cvv.mm"
include "fvex.mm"
include "map0e.mm"
include "mp1i.mm"
include "eqtrd.mm"
include "cfn.mm"
include "0fin.mm"
include "eqid.mm"
include "matbas2.mm"
include "mpan.mm"
include "df1o2.mm"
include "3eqtr3d.mm"

theorem mat0dimbas0
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ( Base ` ( (/) Mat R ) ) = { (/) } )

  proof
    cR
    cV
    wcel
    #
    cR
    cbs
    cfv
    #
    c0
    c0
    cxp
    #
    cmap
    co
    #
    c1o
    c0
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    c0
    csn
    #
    @0
    @3
    @1
    c0
    cmap
    co
    #
    c1o
    @0
    @2
    c0
    @1
    cmap
    @2
    c0
    wceq
    @0
    c0
    0xp
    a1i
    oveq2d
    @1
    cvv
    wcel
    @7
    c1o
    wceq
    @0
    cR
    cbs
    fvex
    @1
    cvv
    map0e
    mp1i
    eqtrd
    c0
    cfn
    wcel
    @0
    @3
    @5
    wceq
    0fin
    @4
    cR
    @1
    c0
    cV
    @4
    eqid
    @1
    eqid
    matbas2
    mpan
    c1o
    @6
    wceq
    @0
    df1o2
    a1i
    3eqtr3d
end
