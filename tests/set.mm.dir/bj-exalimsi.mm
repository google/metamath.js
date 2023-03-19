include "wi.mm"
include "wex.mm"
include "wal.mm"
include "bj-exalims.mm"
include "mpg.mm"

theorem bj-exalimsi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bj-exalimsi.1: |- ( ph -> ( ps -> ch ) )
  assume bj-exalimsi.2: |- ( E. x ph -> ( -. ch -> A. x -. ch ) )


  assert |- ( E. x ph -> ( A. x ps -> ch ) )

  proof
    wph
    wps
    wch
    wi
    wi
    wph
    vx
    wex
    wps
    vx
    wal
    wch
    wi
    wi
    vx
    wph
    wps
    wch
    vx
    bj-exalimsi.2
    bj-exalims
    bj-exalimsi.1
    mpg
end
