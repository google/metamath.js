include "weq.mm"
include "wa.mm"
include "wex.mm"
include "pm5.32i.mm"
include "exbii.mm"
include "ax6ev.mm"
include "19.41v.mm"
include "mpbiran.mm"
include "bitri.mm"

theorem equsexvw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume equsalvw.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint ps x
  assert |- ( E. x ( x = y /\ ph ) <-> ps )

  proof
    vx
    vy
    weq
    #
    wph
    wa
    #
    vx
    wex
    @0
    wps
    wa
    #
    vx
    wex
    #
    wps
    @1
    @2
    vx
    @0
    wph
    wps
    equsalvw.1
    pm5.32i
    exbii
    @3
    @0
    vx
    wex
    wps
    vx
    vy
    ax6ev
    @0
    wps
    vx
    19.41v
    mpbiran
    bitri
end
