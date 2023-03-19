include "wi.mm"
include "wal.mm"
include "wex.mm"
include "bj-exalim.mm"
include "wn.mm"
include "eximal.mm"
include "sylibr.mm"
include "a1i.mm"
include "syldd.mm"

theorem bj-exalims
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bj-exalims.1: |- ( E. x ph -> ( -. ch -> A. x -. ch ) )


  assert |- ( A. x ( ph -> ( ps -> ch ) ) -> ( E. x ph -> ( A. x ps -> ch ) ) )

  proof
    wph
    wps
    wch
    wi
    wi
    vx
    wal
    #
    wph
    vx
    wex
    #
    wps
    vx
    wal
    wch
    vx
    wex
    #
    wch
    wph
    wps
    wch
    vx
    bj-exalim
    @1
    @2
    wch
    wi
    #
    wi
    @0
    @1
    wch
    wn
    #
    @4
    vx
    wal
    wi
    @3
    bj-exalims.1
    wch
    wch
    vx
    eximal
    sylibr
    a1i
    syldd
end
