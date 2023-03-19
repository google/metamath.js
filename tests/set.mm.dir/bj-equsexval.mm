include "weq.mm"
include "wa.mm"
include "wex.mm"
include "wal.mm"
include "pm5.32i.mm"
include "exbii.mm"
include "ax6ev.mm"
include "bj-19.41al.mm"
include "mpbiran.mm"
include "bitri.mm"

theorem bj-equsexval
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-equsexval.1: |- ( x = y -> ( ph <-> A. x ps ) )

  disjoint x y
  assert |- ( E. x ( x = y /\ ph ) <-> A. x ps )

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
    vx
    wal
    #
    wa
    #
    vx
    wex
    #
    @2
    @1
    @3
    vx
    @0
    wph
    @2
    bj-equsexval.1
    pm5.32i
    exbii
    @4
    @0
    vx
    wex
    @2
    vx
    vy
    ax6ev
    @0
    wps
    vx
    bj-19.41al
    mpbiran
    bitri
end
