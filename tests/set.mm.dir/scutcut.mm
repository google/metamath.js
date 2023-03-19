include "csslt.mm"
include "wbr.mm"
include "cscut.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "wa.mm"
include "csur.mm"
include "crab.mm"
include "wcel.mm"
include "w3a.mm"
include "cbday.mm"
include "cfv.mm"
include "cima.mm"
include "cint.mm"
include "wceq.mm"
include "crio.mm"
include "scutval.mm"
include "wreu.mm"
include "conway.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"
include "sneq.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "elrab.mm"
include "3anass.mm"
include "bitr4i.mm"
include "sylib.mm"

theorem scutcut
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y


  assert |- ( A <<s B -> ( ( A |s B ) e. No /\ A <<s { ( A |s B ) } /\ { ( A |s B ) } <<s B ) )

  proof
    cA
    cB
    csslt
    wbr
    #
    cA
    cB
    cscut
    co
    #
    cA
    vy
    cv
    #
    csn
    #
    csslt
    wbr
    #
    @3
    cB
    csslt
    wbr
    #
    wa
    #
    vy
    csur
    crab
    #
    wcel
    #
    @1
    csur
    wcel
    #
    cA
    @1
    csn
    #
    csslt
    wbr
    #
    @10
    cB
    csslt
    wbr
    #
    w3a
    #
    @0
    @1
    vx
    cv
    cbday
    cfv
    cbday
    @7
    cima
    cint
    wceq
    #
    vx
    @7
    crio
    #
    @7
    vx
    vy
    cA
    cB
    scutval
    @0
    @14
    vx
    @7
    wreu
    @15
    @7
    wcel
    vx
    vy
    cA
    cB
    conway
    @14
    vx
    @7
    riotacl
    syl
    eqeltrd
    @8
    @9
    @11
    @12
    wa
    #
    wa
    @13
    @6
    @16
    vy
    @1
    csur
    @2
    @1
    wceq
    #
    @4
    @11
    @5
    @12
    @17
    @3
    @10
    cA
    csslt
    @2
    @1
    sneq
    #
    breq2d
    @17
    @3
    @10
    cB
    csslt
    @18
    breq1d
    anbi12d
    elrab
    @9
    @11
    @12
    3anass
    bitr4i
    sylib
end
