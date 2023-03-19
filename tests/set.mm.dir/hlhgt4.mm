include "chlt.mm"
include "wcel.mm"
include "coml.mm"
include "ccla.mm"
include "cal.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "cple.mm"
include "wbr.mm"
include "catm.mm"
include "wrex.mm"
include "wi.mm"
include "wn.mm"
include "wa.mm"
include "wral.mm"
include "eqid.mm"
include "ishlat2.mm"
include "simprr.mm"
include "sylbi.mm"

theorem hlhgt4
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.lt: class .<
  let c.1: class .1.
  let cK: class K
  let c.0: class .0.
  assume hlhgt4.b: |- B = ( Base ` K )
  assume hlhgt4.s: |- .< = ( lt ` K )
  assume hlhgt4.z: |- .0. = ( 0. ` K )
  assume hlhgt4.u: |- .1. = ( 1. ` K )

  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint K x
  disjoint K y
  disjoint K z
  assert |- ( K e. HL -> E. x e. B E. y e. B E. z e. B ( ( .0. .< x /\ x .< y ) /\ ( y .< z /\ z .< .1. ) ) )

  proof
    cK
    chlt
    wcel
    cK
    coml
    wcel
    cK
    ccla
    wcel
    cK
    cal
    wcel
    w3a
    #
    vx
    cv
    #
    vy
    cv
    #
    wne
    vz
    cv
    #
    @1
    wne
    @3
    @2
    wne
    @3
    @1
    @2
    cK
    cjn
    cfv
    #
    co
    cK
    cple
    cfv
    #
    wbr
    w3a
    vz
    cK
    catm
    cfv
    #
    wrex
    wi
    @1
    @3
    @5
    wbr
    wn
    @1
    @3
    @2
    @4
    co
    @5
    wbr
    wa
    @2
    @3
    @1
    @4
    co
    @5
    wbr
    wi
    vz
    cB
    wral
    wa
    vy
    @6
    wral
    vx
    @6
    wral
    #
    c.0
    @1
    c.lt
    wbr
    @1
    @2
    c.lt
    wbr
    wa
    @2
    @3
    c.lt
    wbr
    @3
    c.1
    c.lt
    wbr
    wa
    wa
    vz
    cB
    wrex
    vy
    cB
    wrex
    vx
    cB
    wrex
    #
    wa
    wa
    @8
    vx
    vy
    vz
    @6
    cB
    c.lt
    c.1
    @4
    cK
    @5
    c.0
    hlhgt4.b
    @5
    eqid
    hlhgt4.s
    @4
    eqid
    hlhgt4.z
    hlhgt4.u
    @6
    eqid
    ishlat2
    @0
    @7
    @8
    simprr
    sylbi
end
