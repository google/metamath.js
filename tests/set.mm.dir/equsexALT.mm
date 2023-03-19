include "weq.mm"
include "wa.mm"
include "wex.mm"
include "pm5.32i.mm"
include "exbii.mm"
include "ax6e.mm"
include "19.41.mm"
include "mpbiran.mm"
include "bitri.mm"

theorem equsexALT
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume equsal.1: |- F/ x ps
  assume equsal.2: |- ( x = y -> ( ph <-> ps ) )


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
    equsal.2
    pm5.32i
    exbii
    @3
    @0
    vx
    wex
    wps
    vx
    vy
    ax6e
    @0
    wps
    vx
    equsal.1
    19.41
    mpbiran
    bitri
end
