include "cmnd.mm"
include "wcel.mm"
include "csubmnd.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "w3a.mm"
include "eqid.mm"
include "issubm.mm"
include "wa.mm"
include "wb.mm"
include "issubmnd.mm"
include "bicomd.mm"
include "3expb.mm"
include "pm5.32da.mm"
include "df-3an.mm"
include "3bitr4g.mm"
include "bitrd.mm"

theorem issubm2
  let cB: class B
  let cS: class S
  let cH: class H
  let cM: class M
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume issubm2.b: |- B = ( Base ` M )
  assume issubm2.z: |- .0. = ( 0g ` M )
  assume issubm2.h: |- H = ( M |`s S )


  assert |- ( M e. Mnd -> ( S e. ( SubMnd ` M ) <-> ( S C_ B /\ .0. e. S /\ H e. Mnd ) ) )

  proof
    cM
    cmnd
    wcel
    #
    cS
    cM
    csubmnd
    cfv
    wcel
    cS
    cB
    wss
    #
    c.0
    cS
    wcel
    #
    vx
    cv
    vy
    cv
    cM
    cplusg
    cfv
    #
    co
    cS
    wcel
    vy
    cS
    wral
    vx
    cS
    wral
    #
    w3a
    #
    @1
    @2
    cH
    cmnd
    wcel
    #
    w3a
    #
    vx
    vy
    cB
    @3
    cS
    cM
    c.0
    issubm2.b
    issubm2.z
    @3
    eqid
    #
    issubm
    @0
    @1
    @2
    wa
    #
    @4
    wa
    @9
    @6
    wa
    @5
    @7
    @0
    @9
    @4
    @6
    @0
    @1
    @2
    @4
    @6
    wb
    @0
    @1
    @2
    w3a
    @6
    @4
    vx
    vy
    cB
    @3
    cS
    cM
    cH
    c.0
    issubm2.b
    @8
    issubm2.z
    issubm2.h
    issubmnd
    bicomd
    3expb
    pm5.32da
    @1
    @2
    @4
    df-3an
    @1
    @2
    @6
    df-3an
    3bitr4g
    bitrd
end
