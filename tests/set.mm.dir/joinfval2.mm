include "wcel.mm"
include "cv.mm"
include "cpr.mm"
include "wbr.mm"
include "coprab.mm"
include "cdm.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "joinfval.mm"
include "wfun.mm"
include "wb.mm"
include "lubfun.mm"
include "funbrfv2b.mm"
include "ax-mp.mm"
include "eqcom.mm"
include "anbi2i.mm"
include "bitri.mm"
include "oprabbii.mm"
include "syl6eq.mm"

theorem joinfval2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cU: class U
  let c.or: class .\/
  let cK: class K
  let cV: class V
  let vp: setvar p
  assume joinfval.u: |- U = ( lub ` K )
  assume joinfval.j: |- .\/ = ( join ` K )

  disjoint x y
  disjoint x z
  disjoint K x
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint U z
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint K p
  disjoint U p
  assert |- ( K e. V -> .\/ = { <. <. x , y >. , z >. | ( { x , y } e. dom U /\ z = ( U ` { x , y } ) ) } )

  proof
    cK
    cV
    wcel
    c.or
    vx
    cv
    vy
    cv
    cpr
    #
    vz
    cv
    #
    cU
    wbr
    #
    vx
    vy
    vz
    coprab
    @0
    cU
    cdm
    wcel
    #
    @1
    @0
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
    vx
    vy
    vz
    cU
    c.or
    cK
    cV
    joinfval.u
    joinfval.j
    joinfval
    @2
    @6
    vx
    vy
    vz
    @2
    @3
    @4
    @1
    wceq
    #
    wa
    #
    @6
    cU
    wfun
    @2
    @8
    wb
    cU
    cK
    joinfval.u
    lubfun
    @0
    @1
    cU
    funbrfv2b
    ax-mp
    @7
    @5
    @3
    @4
    @1
    eqcom
    anbi2i
    bitri
    oprabbii
    syl6eq
end
