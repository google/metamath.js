include "cv.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "cop.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "crab.mm"
include "copab.mm"
include "elxp.mm"
include "anbi1i.mm"
include "19.41vv.mm"
include "anass.mm"
include "anbi2d.mm"
include "df-3an.mm"
include "syl6bbr.mm"
include "pm5.32i.mm"
include "bitri.mm"
include "2exbii.mm"
include "3bitr2i.mm"
include "abbii.mm"
include "df-rab.mm"
include "df-opab.mm"
include "3eqtr4i.mm"

theorem rabxp
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume rabxp.1: |- ( x = <. y , z >. -> ( ph <-> ps ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint ph y
  disjoint ph z
  disjoint ps x
  assert |- { x e. ( A X. B ) | ph } = { <. y , z >. | ( y e. A /\ z e. B /\ ps ) }

  proof
    vx
    cv
    #
    cA
    cB
    cxp
    #
    wcel
    #
    wph
    wa
    #
    vx
    cab
    @0
    vy
    cv
    #
    vz
    cv
    #
    cop
    wceq
    #
    @4
    cA
    wcel
    #
    @5
    cB
    wcel
    #
    wps
    w3a
    #
    wa
    #
    vz
    wex
    vy
    wex
    #
    vx
    cab
    wph
    vx
    @1
    crab
    @9
    vy
    vz
    copab
    @3
    @11
    vx
    @3
    @6
    @7
    @8
    wa
    #
    wa
    #
    vz
    wex
    vy
    wex
    #
    wph
    wa
    @13
    wph
    wa
    #
    vz
    wex
    vy
    wex
    @11
    @2
    @14
    wph
    vy
    vz
    @0
    cA
    cB
    elxp
    anbi1i
    @13
    wph
    vy
    vz
    19.41vv
    @15
    @10
    vy
    vz
    @15
    @6
    @12
    wph
    wa
    #
    wa
    @10
    @6
    @12
    wph
    anass
    @6
    @16
    @9
    @6
    @16
    @12
    wps
    wa
    @9
    @6
    wph
    wps
    @12
    rabxp.1
    anbi2d
    @7
    @8
    wps
    df-3an
    syl6bbr
    pm5.32i
    bitri
    2exbii
    3bitr2i
    abbii
    wph
    vx
    @1
    df-rab
    @9
    vy
    vz
    vx
    df-opab
    3eqtr4i
end
