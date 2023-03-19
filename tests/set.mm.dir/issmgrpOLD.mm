include "csem.mm"
include "wcel.mm"
include "cmagm.mm"
include "cass.mm"
include "cin.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "df-sgrOLD.mm"
include "eleq2i.mm"
include "elin.mm"
include "ismgmOLD.mm"
include "isass.mm"
include "anbi12d.mm"
include "syl5bb.mm"

theorem issmgrpOLD
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cG: class G
  let cX: class X
  assume issmgrpOLD.1: |- X = dom dom G

  disjoint G x
  disjoint G y
  disjoint G z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( G e. A -> ( G e. SemiGrp <-> ( G : ( X X. X ) --> X /\ A. x e. X A. y e. X A. z e. X ( ( x G y ) G z ) = ( x G ( y G z ) ) ) ) )

  proof
    cG
    csem
    wcel
    cG
    cmagm
    cass
    cin
    #
    wcel
    #
    cG
    cA
    wcel
    #
    cX
    cX
    cxp
    cX
    cG
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    vz
    cv
    #
    cG
    co
    @4
    @5
    @6
    cG
    co
    cG
    co
    wceq
    vz
    cX
    wral
    vy
    cX
    wral
    vx
    cX
    wral
    #
    wa
    #
    csem
    @0
    cG
    df-sgrOLD
    eleq2i
    @1
    cG
    cmagm
    wcel
    #
    cG
    cass
    wcel
    #
    wa
    @2
    @8
    cG
    cmagm
    cass
    elin
    @2
    @9
    @3
    @10
    @7
    cA
    cG
    cX
    issmgrpOLD.1
    ismgmOLD
    vx
    vy
    vz
    cA
    cG
    cX
    issmgrpOLD.1
    isass
    anbi12d
    syl5bb
    syl5bb
end
