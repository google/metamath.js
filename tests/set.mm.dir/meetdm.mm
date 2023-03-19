include "wcel.mm"
include "cdm.mm"
include "cv.mm"
include "cpr.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "coprab.mm"
include "copab.mm"
include "meetfval2.mm"
include "dmeqd.mm"
include "wex.mm"
include "dmoprab.mm"
include "fvex.mm"
include "isseti.mm"
include "19.42v.mm"
include "mpbiran2.mm"
include "opabbii.mm"
include "eqtri.mm"
include "syl6eq.mm"

theorem meetdm
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cK: class K
  let c.an: class ./\
  let cV: class V
  let vp: setvar p
  let vz: setvar z
  assume meetfval.u: |- G = ( glb ` K )
  assume meetfval.m: |- ./\ = ( meet ` K )

  disjoint x y
  disjoint K x
  disjoint K y
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint K p
  disjoint x z
  disjoint y z
  disjoint K z
  disjoint G p
  disjoint G z
  assert |- ( K e. V -> dom ./\ = { <. x , y >. | { x , y } e. dom G } )

  proof
    cK
    cV
    wcel
    #
    c.an
    cdm
    vx
    cv
    vy
    cv
    cpr
    #
    cG
    cdm
    wcel
    #
    vz
    cv
    @1
    cG
    cfv
    #
    wceq
    #
    wa
    #
    vx
    vy
    vz
    coprab
    #
    cdm
    #
    @2
    vx
    vy
    copab
    #
    @0
    c.an
    @6
    vx
    vy
    vz
    cG
    cK
    c.an
    cV
    meetfval.u
    meetfval.m
    meetfval2
    dmeqd
    @7
    @5
    vz
    wex
    #
    vx
    vy
    copab
    @8
    @5
    vx
    vy
    vz
    dmoprab
    @9
    @2
    vx
    vy
    @9
    @2
    @4
    vz
    wex
    vz
    @3
    @1
    cG
    fvex
    isseti
    @2
    @4
    vz
    19.42v
    mpbiran2
    opabbii
    eqtri
    syl6eq
end
