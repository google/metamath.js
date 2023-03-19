include "wi.mm"
include "wal.mm"
include "wn.mm"
include "wo.mm"
include "imor.mm"
include "albii.mm"
include "nexr.mm"
include "orci.mm"
include "mpgbir.mm"
include "pm3.2i.mm"

theorem alimp-surprise
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vk: setvar k
  assume alimp-surprise.1: |- -. E. x ph


  assert |- ( A. x ( ph -> ps ) /\ A. x ( ph -> -. ps ) )

  proof
    wph
    wps
    wi
    #
    vx
    wal
    #
    wph
    wps
    wn
    #
    wi
    #
    vx
    wal
    #
    @1
    wph
    wn
    #
    wps
    wo
    #
    vx
    @0
    @6
    vx
    wph
    wps
    imor
    albii
    @5
    wps
    wph
    vx
    alimp-surprise.1
    nexr
    #
    orci
    mpgbir
    @4
    @5
    @2
    wo
    #
    vx
    @3
    @8
    vx
    wph
    @2
    imor
    albii
    @5
    @2
    @7
    orci
    mpgbir
    pm3.2i
end
