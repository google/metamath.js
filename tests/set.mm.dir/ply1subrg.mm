include "crg.mm"
include "wcel.mm"
include "c1o.mm"
include "cmps.mm"
include "co.mm"
include "csubrg.mm"
include "cfv.mm"
include "cmpl.mm"
include "con0.mm"
include "eqid.mm"
include "ply1bas.mm"
include "1on.mm"
include "a1i.mm"
include "id.mm"
include "mplsubrg.mm"
include "cbs.mm"
include "eqidd.mm"
include "c0.mm"
include "psr1val.mm"
include "cxp.mm"
include "wss.mm"
include "0ss.mm"
include "opsrbas.mm"
include "cv.mm"
include "wa.mm"
include "cplusg.mm"
include "opsrplusg.mm"
include "oveqdr.mm"
include "cmulr.mm"
include "opsrmulr.mm"
include "subrgpropd.mm"
include "eleqtrd.mm"

theorem ply1subrg
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume ply1val.1: |- P = ( Poly1 ` R )
  assume ply1val.2: |- S = ( PwSer1 ` R )
  assume ply1bas.u: |- U = ( Base ` P )


  assert |- ( R e. Ring -> U e. ( SubRing ` S ) )

  proof
    cR
    crg
    wcel
    #
    cU
    c1o
    cR
    cmps
    co
    #
    csubrg
    cfv
    cS
    csubrg
    cfv
    @0
    c1o
    cR
    cmpl
    co
    #
    cR
    @1
    cU
    c1o
    con0
    @1
    eqid
    #
    @2
    eqid
    cP
    cR
    cS
    cU
    ply1val.1
    ply1val.2
    ply1bas.u
    ply1bas
    c1o
    con0
    wcel
    @0
    1on
    a1i
    @0
    id
    mplsubrg
    @0
    vx
    vy
    @1
    cbs
    cfv
    #
    @1
    cS
    @0
    @4
    eqidd
    @0
    cR
    @1
    c0
    c1o
    cS
    @3
    cR
    cS
    ply1val.2
    psr1val
    #
    c0
    c1o
    c1o
    cxp
    #
    wss
    @0
    @6
    0ss
    a1i
    #
    opsrbas
    @0
    vx
    cv
    @4
    wcel
    vy
    cv
    @4
    wcel
    wa
    #
    vx
    vy
    @1
    cplusg
    cfv
    cS
    cplusg
    cfv
    @0
    cR
    @1
    c0
    c1o
    cS
    @3
    @5
    @7
    opsrplusg
    oveqdr
    @0
    @8
    vx
    vy
    @1
    cmulr
    cfv
    cS
    cmulr
    cfv
    @0
    cR
    @1
    c0
    c1o
    cS
    @3
    @5
    @7
    opsrmulr
    oveqdr
    subrgpropd
    eleqtrd
end
