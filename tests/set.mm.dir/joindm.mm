include "wcel.mm"
include "cdm.mm"
include "cv.mm"
include "cpr.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "coprab.mm"
include "copab.mm"
include "joinfval2.mm"
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

theorem joindm
  let vx: setvar x
  let vy: setvar y
  let cU: class U
  let c.or: class .\/
  let cK: class K
  let cV: class V
  let vp: setvar p
  let vz: setvar z
  assume joinfval.u: |- U = ( lub ` K )
  assume joinfval.j: |- .\/ = ( join ` K )

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
  disjoint U p
  disjoint U z
  assert |- ( K e. V -> dom .\/ = { <. x , y >. | { x , y } e. dom U } )

  proof
    cK
    cV
    wcel
    #
    c.or
    cdm
    vx
    cv
    vy
    cv
    cpr
    #
    cU
    cdm
    wcel
    #
    vz
    cv
    @1
    cU
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
    c.or
    @6
    vx
    vy
    vz
    cU
    c.or
    cK
    cV
    joinfval.u
    joinfval.j
    joinfval2
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
    cU
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
