include "crg.mm"
include "wcel.mm"
include "c0.mm"
include "c1o.mm"
include "cmvr.mm"
include "co.mm"
include "cfv.mm"
include "vr1val.mm"
include "cmps.mm"
include "cbs.mm"
include "con0.mm"
include "eqid.mm"
include "1on.mm"
include "a1i.mm"
include "id.mm"
include "0lt1o.mm"
include "mvrcl2.mm"
include "psr1val.mm"
include "cxp.mm"
include "wss.mm"
include "0ss.mm"
include "opsrbas.mm"
include "syl6eqr.mm"
include "eleqtrd.mm"
include "syl5eqel.mm"

theorem vr1cl2
  let cB: class B
  let cR: class R
  let cS: class S
  let cX: class X
  let vf: setvar f
  let vh: setvar h
  let vi: setvar i
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume vr1val.1: |- X = ( var1 ` R )
  assume vr1cl2.2: |- S = ( PwSer1 ` R )
  assume vr1cl2.3: |- B = ( Base ` S )


  assert |- ( R e. Ring -> X e. B )

  proof
    cR
    crg
    wcel
    #
    cX
    c0
    c1o
    cR
    cmvr
    co
    #
    cfv
    #
    cB
    cR
    cX
    vr1val.1
    vr1val
    @0
    @2
    c1o
    cR
    cmps
    co
    #
    cbs
    cfv
    #
    cB
    @0
    @4
    cR
    @3
    c1o
    @1
    con0
    c0
    @3
    eqid
    #
    @1
    eqid
    @4
    eqid
    c1o
    con0
    wcel
    @0
    1on
    a1i
    @0
    id
    c0
    c1o
    wcel
    @0
    0lt1o
    a1i
    mvrcl2
    @0
    @4
    cS
    cbs
    cfv
    cB
    @0
    cR
    @3
    c0
    c1o
    cS
    @5
    cR
    cS
    vr1cl2.2
    psr1val
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
    opsrbas
    vr1cl2.3
    syl6eqr
    eleqtrd
    syl5eqel
end
