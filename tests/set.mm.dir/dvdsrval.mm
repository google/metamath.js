include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "copab.mm"
include "cdsr.mm"
include "cfv.mm"
include "cbs.mm"
include "cmulr.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "rexeqdv.mm"
include "anbi12d.mm"
include "oveqd.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "anbi2d.mm"
include "bitrd.mm"
include "opabbidv.mm"
include "df-dvdsr.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cab.mm"
include "eqcom.mm"
include "rexbii.mm"
include "abbii.mm"
include "abrexex.mm"
include "a1i.mm"
include "opabex3.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "wne.mm"
include "wex.mm"
include "opabn0.mm"
include "n0i.mm"
include "nsyl2.mm"
include "adantr.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "necon1bi.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem dvdsrval
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pa: class .||
  let cR: class R
  let c.x: class .x.
  let vr: setvar r
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume dvdsr.1: |- B = ( Base ` R )
  assume dvdsr.2: |- .|| = ( ||r ` R )
  assume dvdsr.3: |- .x. = ( .r ` R )

  disjoint x y
  disjoint .|| x
  disjoint .|| y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint B r
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint Z x
  disjoint Z y
  disjoint R r
  disjoint .x. r
  assert |- .|| = { <. x , y >. | ( x e. B /\ E. z e. B ( z .x. x ) = y ) }

  proof
    cR
    cvv
    wcel
    #
    c.pa
    vx
    cv
    #
    cB
    wcel
    #
    vz
    cv
    #
    @1
    c.x
    co
    #
    vy
    cv
    #
    wceq
    #
    vz
    cB
    wrex
    #
    wa
    #
    vx
    vy
    copab
    #
    wceq
    @0
    c.pa
    cR
    cdsr
    cfv
    #
    @9
    dvdsr.2
    vr
    cR
    @1
    vr
    cv
    #
    cbs
    cfv
    #
    wcel
    #
    @3
    @1
    @11
    cmulr
    cfv
    #
    co
    #
    @5
    wceq
    #
    vz
    @12
    wrex
    #
    wa
    #
    vx
    vy
    copab
    @9
    cvv
    cdsr
    @11
    cR
    wceq
    #
    @18
    @8
    vx
    vy
    @19
    @18
    @2
    @16
    vz
    cB
    wrex
    #
    wa
    @8
    @19
    @13
    @2
    @17
    @20
    @19
    @12
    cB
    @1
    @19
    @12
    cR
    cbs
    cfv
    #
    cB
    @11
    cR
    cbs
    fveq2
    dvdsr.1
    syl6eqr
    #
    eleq2d
    @19
    @16
    vz
    @12
    cB
    @22
    rexeqdv
    anbi12d
    @19
    @20
    @7
    @2
    @19
    @16
    @6
    vz
    cB
    @19
    @15
    @4
    @5
    @19
    @14
    c.x
    @3
    @1
    @19
    @14
    cR
    cmulr
    cfv
    c.x
    @11
    cR
    cmulr
    fveq2
    dvdsr.3
    syl6eqr
    oveqd
    eqeq1d
    rexbidv
    anbi2d
    bitrd
    opabbidv
    vx
    vy
    vz
    vr
    df-dvdsr
    @7
    vx
    vy
    cB
    cB
    @21
    cvv
    dvdsr.1
    cR
    cbs
    fvex
    eqeltri
    #
    @7
    vy
    cab
    #
    cvv
    wcel
    @2
    @24
    @5
    @4
    wceq
    #
    vz
    cB
    wrex
    #
    vy
    cab
    cvv
    @7
    @26
    vy
    @6
    @25
    vz
    cB
    @4
    @5
    eqcom
    rexbii
    abbii
    vz
    vy
    cB
    @4
    @23
    abrexex
    eqeltri
    a1i
    opabex3
    fvmpt
    syl5eq
    @0
    wn
    #
    c.pa
    c0
    @9
    @27
    c.pa
    @10
    c0
    dvdsr.2
    cR
    cdsr
    fvprc
    syl5eq
    @0
    @9
    c0
    @9
    c0
    wne
    @8
    vy
    wex
    vx
    wex
    @0
    @8
    vx
    vy
    opabn0
    @8
    @0
    vx
    vy
    @2
    @0
    @7
    @2
    cB
    c0
    wceq
    @0
    cB
    @1
    n0i
    @27
    cB
    @21
    c0
    dvdsr.1
    cR
    cbs
    fvprc
    syl5eq
    nsyl2
    adantr
    exlimivv
    sylbi
    necon1bi
    eqtr4d
    pm2.61i
end
