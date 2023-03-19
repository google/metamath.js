include "crab.mm"
include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "wn.mm"
include "df-rab.mm"
include "difeq12i.mm"
include "difab.mm"
include "anass.mm"
include "simpr.mm"
include "con3i.mm"
include "anim2i.mm"
include "wi.mm"
include "pm3.2.mm"
include "adantr.mm"
include "con3d.mm"
include "imdistani.mm"
include "impbii.mm"
include "bitr3i.mm"
include "abbii.mm"
include "eqtr4i.mm"

theorem difrab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( { x e. A | ph } \ { x e. A | ps } ) = { x e. A | ( ph /\ -. ps ) }

  proof
    wph
    vx
    cA
    crab
    #
    wps
    vx
    cA
    crab
    #
    cdif
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    @2
    wps
    wa
    #
    vx
    cab
    #
    cdif
    #
    wph
    wps
    wn
    #
    wa
    #
    vx
    cA
    crab
    #
    @0
    @4
    @1
    @6
    wph
    vx
    cA
    df-rab
    wps
    vx
    cA
    df-rab
    difeq12i
    @10
    @2
    @9
    wa
    #
    vx
    cab
    #
    @7
    @9
    vx
    cA
    df-rab
    @7
    @3
    @5
    wn
    #
    wa
    #
    vx
    cab
    @12
    @3
    @5
    vx
    difab
    @11
    @14
    vx
    @11
    @3
    @8
    wa
    #
    @14
    @2
    wph
    @8
    anass
    @15
    @14
    @8
    @13
    @3
    @5
    wps
    @2
    wps
    simpr
    con3i
    anim2i
    @3
    @13
    @8
    @3
    wps
    @5
    @2
    wps
    @5
    wi
    wph
    @2
    wps
    pm3.2
    adantr
    con3d
    imdistani
    impbii
    bitr3i
    abbii
    eqtr4i
    eqtr4i
    eqtr4i
end
