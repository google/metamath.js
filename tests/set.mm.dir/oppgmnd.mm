include "cmnd.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "c0g.mm"
include "wceq.mm"
include "eqid.mm"
include "oppgbas.mm"
include "a1i.mm"
include "eqidd.mm"
include "cv.mm"
include "w3a.mm"
include "co.mm"
include "oppgplus.mm"
include "mndcl.mm"
include "3com23.mm"
include "syl5eqel.mm"
include "wa.mm"
include "simpl.mm"
include "simpr3.mm"
include "simpr2.mm"
include "simpr1.mm"
include "mndass.mm"
include "syl13anc.mm"
include "eqcomd.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "3eqtr4g.mm"
include "mndidcl.mm"
include "mndrid.mm"
include "syl5eq.mm"
include "mndlid.mm"
include "ismndd.mm"

theorem oppgmnd
  let cR: class R
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume oppgbas.1: |- O = ( oppG ` R )


  assert |- ( R e. Mnd -> O e. Mnd )

  proof
    cR
    cmnd
    wcel
    #
    vx
    vy
    vz
    cR
    cbs
    cfv
    #
    cO
    cplusg
    cfv
    #
    cO
    cR
    c0g
    cfv
    #
    @1
    cO
    cbs
    cfv
    wceq
    @0
    @1
    cR
    cO
    oppgbas.1
    @1
    eqid
    #
    oppgbas
    a1i
    @0
    @2
    eqidd
    @0
    vx
    cv
    #
    @1
    wcel
    #
    vy
    cv
    #
    @1
    wcel
    #
    w3a
    @5
    @7
    @2
    co
    #
    @7
    @5
    cR
    cplusg
    cfv
    #
    co
    #
    @1
    @10
    @2
    cR
    cO
    @5
    @7
    @10
    eqid
    #
    oppgbas.1
    @2
    eqid
    #
    oppgplus
    #
    @0
    @8
    @6
    @11
    @1
    wcel
    @1
    @10
    cR
    @7
    @5
    @4
    @12
    mndcl
    3com23
    syl5eqel
    @0
    @6
    @8
    vz
    cv
    #
    @1
    wcel
    #
    w3a
    #
    wa
    #
    @15
    @11
    @10
    co
    #
    @15
    @7
    @10
    co
    #
    @5
    @10
    co
    #
    @9
    @15
    @2
    co
    #
    @5
    @7
    @15
    @2
    co
    #
    @2
    co
    #
    @18
    @21
    @19
    @18
    @0
    @16
    @8
    @6
    @21
    @19
    wceq
    @0
    @17
    simpl
    @0
    @6
    @8
    @16
    simpr3
    @0
    @6
    @8
    @16
    simpr2
    @0
    @6
    @8
    @16
    simpr1
    @1
    @10
    cR
    @15
    @7
    @5
    @4
    @12
    mndass
    syl13anc
    eqcomd
    @22
    @11
    @15
    @2
    co
    @19
    @9
    @11
    @15
    @2
    @14
    oveq1i
    @10
    @2
    cR
    cO
    @11
    @15
    @12
    oppgbas.1
    @13
    oppgplus
    eqtri
    @24
    @5
    @20
    @2
    co
    @21
    @23
    @20
    @5
    @2
    @10
    @2
    cR
    cO
    @7
    @15
    @12
    oppgbas.1
    @13
    oppgplus
    oveq2i
    @10
    @2
    cR
    cO
    @5
    @20
    @12
    oppgbas.1
    @13
    oppgplus
    eqtri
    3eqtr4g
    @1
    cR
    @3
    @4
    @3
    eqid
    #
    mndidcl
    @0
    @6
    wa
    #
    @3
    @5
    @2
    co
    @5
    @3
    @10
    co
    @5
    @10
    @2
    cR
    cO
    @3
    @5
    @12
    oppgbas.1
    @13
    oppgplus
    @1
    @10
    cR
    @5
    @3
    @4
    @12
    @25
    mndrid
    syl5eq
    @26
    @5
    @3
    @2
    co
    @3
    @5
    @10
    co
    @5
    @10
    @2
    cR
    cO
    @5
    @3
    @12
    oppgbas.1
    @13
    oppgplus
    @1
    @10
    cR
    @5
    @3
    @4
    @12
    @25
    mndlid
    syl5eq
    ismndd
end
