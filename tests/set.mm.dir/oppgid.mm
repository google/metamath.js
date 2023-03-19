include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "wcel.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "cio.mm"
include "c0g.mm"
include "ancom.mm"
include "eqid.mm"
include "oppgplus.mm"
include "eqeq1i.mm"
include "anbi12i.mm"
include "bitr4i.mm"
include "ralbii.mm"
include "anbi2i.mm"
include "iotabii.mm"
include "grpidval.mm"
include "oppgbas.mm"
include "3eqtr4i.mm"

theorem oppgid
  let cR: class R
  let cO: class O
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cI: class I
  assume oppgbas.1: |- O = ( oppG ` R )
  assume oppgid.2: |- .0. = ( 0g ` R )


  assert |- .0. = ( 0g ` O )

  proof
    vx
    cv
    #
    cR
    cbs
    cfv
    #
    wcel
    #
    @0
    vy
    cv
    #
    cR
    cplusg
    cfv
    #
    co
    #
    @3
    wceq
    #
    @3
    @0
    @4
    co
    #
    @3
    wceq
    #
    wa
    #
    vy
    @1
    wral
    #
    wa
    #
    vx
    cio
    @2
    @0
    @3
    cO
    cplusg
    cfv
    #
    co
    #
    @3
    wceq
    #
    @3
    @0
    @12
    co
    #
    @3
    wceq
    #
    wa
    #
    vy
    @1
    wral
    #
    wa
    #
    vx
    cio
    c.0
    cO
    c0g
    cfv
    #
    @11
    @19
    vx
    @10
    @18
    @2
    @9
    @17
    vy
    @1
    @9
    @8
    @6
    wa
    @17
    @6
    @8
    ancom
    @14
    @8
    @16
    @6
    @13
    @7
    @3
    @4
    @12
    cR
    cO
    @0
    @3
    @4
    eqid
    #
    oppgbas.1
    @12
    eqid
    #
    oppgplus
    eqeq1i
    @15
    @5
    @3
    @4
    @12
    cR
    cO
    @3
    @0
    @21
    oppgbas.1
    @22
    oppgplus
    eqeq1i
    anbi12i
    bitr4i
    ralbii
    anbi2i
    iotabii
    vy
    @1
    @4
    vx
    cR
    c.0
    @1
    eqid
    #
    @21
    oppgid.2
    grpidval
    vy
    @1
    @12
    vx
    cO
    @20
    @1
    cR
    cO
    oppgbas.1
    @23
    oppgbas
    @22
    @20
    eqid
    grpidval
    3eqtr4i
end
