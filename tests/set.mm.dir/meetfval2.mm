include "wcel.mm"
include "cv.mm"
include "cpr.mm"
include "wbr.mm"
include "coprab.mm"
include "cdm.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "meetfval.mm"
include "wfun.mm"
include "wb.mm"
include "glbfun.mm"
include "funbrfv2b.mm"
include "ax-mp.mm"
include "eqcom.mm"
include "anbi2i.mm"
include "bitri.mm"
include "oprabbii.mm"
include "syl6eq.mm"

theorem meetfval2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cK: class K
  let c.an: class ./\
  let cV: class V
  let vp: setvar p
  assume meetfval.u: |- G = ( glb ` K )
  assume meetfval.m: |- ./\ = ( meet ` K )

  disjoint x y
  disjoint x z
  disjoint K x
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint G z
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint K p
  disjoint G p
  assert |- ( K e. V -> ./\ = { <. <. x , y >. , z >. | ( { x , y } e. dom G /\ z = ( G ` { x , y } ) ) } )

  proof
    cK
    cV
    wcel
    c.an
    vx
    cv
    vy
    cv
    cpr
    #
    vz
    cv
    #
    cG
    wbr
    #
    vx
    vy
    vz
    coprab
    @0
    cG
    cdm
    wcel
    #
    @1
    @0
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
    vx
    vy
    vz
    cG
    cK
    c.an
    cV
    meetfval.u
    meetfval.m
    meetfval
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
    cG
    wfun
    @2
    @8
    wb
    cG
    cK
    meetfval.u
    glbfun
    @0
    @1
    cG
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
