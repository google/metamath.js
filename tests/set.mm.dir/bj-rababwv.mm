include "cab.mm"
include "crab.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "df-rab.mm"
include "bj-vexwv.mm"
include "biantrur.mm"
include "bj-abbii.mm"
include "eqtr4i.mm"

theorem bj-rababwv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-rababwv.1: |- ps

  disjoint x y
  assert |- { x e. { y | ps } | ph } = { x | ph }

  proof
    wph
    vx
    wps
    vy
    cab
    #
    crab
    vx
    cv
    @0
    wcel
    #
    wph
    wa
    #
    vx
    cab
    wph
    vx
    cab
    wph
    vx
    @0
    df-rab
    wph
    @2
    vx
    @1
    wph
    wps
    vy
    vx
    bj-rababwv.1
    bj-vexwv
    biantrur
    bj-abbii
    eqtr4i
end
