include "cv.mm"
include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "copab.mm"
include "cdvds.mm"
include "zring.mm"
include "cdsr.mm"
include "cfv.mm"
include "simpl.mm"
include "anim1i.mm"
include "zmulcl.mm"
include "ancoms.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "imp.mm"
include "simpr.mm"
include "jca31.mm"
include "impbii.mm"
include "opabbii.mm"
include "df-dvds.mm"
include "zringbas.mm"
include "eqid.mm"
include "zringmulr.mm"
include "dvdsrval.mm"
include "3eqtr4i.mm"

theorem dvdsrzring
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- || = ( ||r ` ZZring )

  proof
    vx
    cv
    #
    cz
    wcel
    #
    vy
    cv
    #
    cz
    wcel
    #
    wa
    #
    vz
    cv
    #
    @0
    cmul
    co
    #
    @2
    wceq
    #
    vz
    cz
    wrex
    #
    wa
    #
    vx
    vy
    copab
    @1
    @8
    wa
    #
    vx
    vy
    copab
    cdvds
    zring
    cdsr
    cfv
    #
    @9
    @10
    vx
    vy
    @9
    @10
    @4
    @1
    @8
    @1
    @3
    simpl
    anim1i
    @10
    @1
    @3
    @8
    @1
    @8
    simpl
    @1
    @8
    @3
    @1
    @7
    @3
    vz
    cz
    @1
    @5
    cz
    wcel
    #
    wa
    @6
    cz
    wcel
    #
    @7
    @3
    @12
    @1
    @13
    @5
    @0
    zmulcl
    ancoms
    @6
    @2
    cz
    eleq1
    syl5ibcom
    rexlimdva
    imp
    @1
    @8
    simpr
    jca31
    impbii
    opabbii
    vx
    vy
    vz
    df-dvds
    vx
    vy
    vz
    cz
    @11
    zring
    cmul
    zringbas
    @11
    eqid
    zringmulr
    dvdsrval
    3eqtr4i
end
