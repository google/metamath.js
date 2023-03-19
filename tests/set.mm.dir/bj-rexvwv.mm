include "cab.mm"
include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "df-rex.mm"
include "bj-vexwv.mm"
include "biantrur.mm"
include "exbii.mm"
include "bitr4i.mm"

theorem bj-rexvwv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-rexvwv.1: |- ps

  disjoint x y
  assert |- ( E. x e. { y | ps } ph <-> E. x ph )

  proof
    wph
    vx
    wps
    vy
    cab
    #
    wrex
    vx
    cv
    @0
    wcel
    #
    wph
    wa
    #
    vx
    wex
    wph
    vx
    wex
    wph
    vx
    @0
    df-rex
    wph
    @2
    vx
    @1
    wph
    wps
    vy
    vx
    bj-rexvwv.1
    bj-vexwv
    biantrur
    exbii
    bitr4i
end
