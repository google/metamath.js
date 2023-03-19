include "crg.mm"
include "wcel.mm"
include "c1o.mm"
include "cmps.mm"
include "co.mm"
include "clss.mm"
include "cfv.mm"
include "cmpl.mm"
include "con0.mm"
include "eqid.mm"
include "ply1bas.mm"
include "1on.mm"
include "a1i.mm"
include "id.mm"
include "mpllss.mm"
include "cbs.mm"
include "cvv.mm"
include "eqidd.mm"
include "c0.mm"
include "psr1val.mm"
include "cxp.mm"
include "wss.mm"
include "0ss.mm"
include "opsrbas.mm"
include "ssv.mm"
include "cv.mm"
include "wa.mm"
include "cplusg.mm"
include "opsrplusg.mm"
include "oveqdr.mm"
include "cvsca.mm"
include "ovexd.mm"
include "opsrvsca.mm"
include "csca.mm"
include "psrsca.mm"
include "fveq2d.mm"
include "opsrsca.mm"
include "lsspropd.mm"
include "eleqtrd.mm"

theorem ply1lss
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


  assert |- ( R e. Ring -> U e. ( LSubSp ` S ) )

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
    clss
    cfv
    cS
    clss
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
    #
    @0
    id
    #
    mpllss
    @0
    vx
    vy
    @1
    cbs
    cfv
    #
    cR
    cbs
    cfv
    #
    @1
    cS
    cvv
    @0
    @6
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
    @9
    0ss
    a1i
    #
    opsrbas
    @6
    cvv
    wss
    @0
    @6
    ssv
    a1i
    @0
    vx
    cv
    #
    cvv
    wcel
    vy
    cv
    #
    cvv
    wcel
    wa
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
    @8
    @10
    opsrplusg
    oveqdr
    @0
    @11
    @7
    wcel
    @12
    @6
    wcel
    wa
    #
    wa
    @11
    @12
    @1
    cvsca
    cfv
    #
    ovexd
    @0
    @13
    vx
    vy
    @14
    cS
    cvsca
    cfv
    @0
    cR
    @1
    c0
    c1o
    cS
    @3
    @8
    @10
    opsrvsca
    oveqdr
    @0
    cR
    @1
    csca
    cfv
    cbs
    @0
    cR
    @1
    c1o
    con0
    crg
    @3
    @4
    @5
    psrsca
    fveq2d
    @0
    cR
    cS
    csca
    cfv
    cbs
    @0
    cR
    @1
    c0
    c1o
    cS
    con0
    crg
    @3
    @8
    @10
    @4
    @5
    opsrsca
    fveq2d
    lsspropd
    eleqtrd
end
