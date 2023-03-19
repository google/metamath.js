include "cmnd.mm"
include "wcel.mm"
include "oppgmnd.mm"
include "coppg.mm"
include "cfv.mm"
include "eqid.mm"
include "wb.mm"
include "wtru.mm"
include "cbs.mm"
include "wceq.mm"
include "oppgbas.mm"
include "a1i.mm"
include "eqidd.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wa.mm"
include "oppgplus.mm"
include "eqtri.mm"
include "mndpropd.mm"
include "trud.mm"
include "sylib.mm"
include "impbii.mm"

theorem oppgmndb
  let cR: class R
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume oppgbas.1: |- O = ( oppG ` R )


  assert |- ( R e. Mnd <-> O e. Mnd )

  proof
    cR
    cmnd
    wcel
    #
    cO
    cmnd
    wcel
    #
    cR
    cO
    oppgbas.1
    oppgmnd
    @1
    cO
    coppg
    cfv
    #
    cmnd
    wcel
    #
    @0
    cO
    @2
    @2
    eqid
    #
    oppgmnd
    @3
    @0
    wb
    wtru
    vx
    vy
    cR
    cbs
    cfv
    #
    @2
    cR
    @5
    @2
    cbs
    cfv
    wceq
    wtru
    @5
    cO
    @2
    @4
    @5
    cR
    cO
    oppgbas.1
    @5
    eqid
    oppgbas
    oppgbas
    a1i
    wtru
    @5
    eqidd
    vx
    cv
    #
    vy
    cv
    #
    @2
    cplusg
    cfv
    #
    co
    #
    @6
    @7
    cR
    cplusg
    cfv
    #
    co
    #
    wceq
    wtru
    @6
    @5
    wcel
    @7
    @5
    wcel
    wa
    wa
    @9
    @7
    @6
    cO
    cplusg
    cfv
    #
    co
    @11
    @12
    @8
    cO
    @2
    @6
    @7
    @12
    eqid
    #
    @4
    @8
    eqid
    oppgplus
    @10
    @12
    cR
    cO
    @7
    @6
    @10
    eqid
    oppgbas.1
    @13
    oppgplus
    eqtri
    a1i
    mndpropd
    trud
    sylib
    impbii
end
