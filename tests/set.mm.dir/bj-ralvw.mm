include "cab.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "bj-vexw.mm"
include "a1bi.mm"
include "albii.mm"
include "bitr4i.mm"

theorem bj-ralvw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-ralvw.1: |- ps


  assert |- ( A. x e. { y | ps } ph <-> A. x ph )

  proof
    wph
    vx
    wps
    vy
    cab
    #
    wral
    vx
    cv
    @0
    wcel
    #
    wph
    wi
    #
    vx
    wal
    wph
    vx
    wal
    wph
    vx
    @0
    df-ral
    wph
    @2
    vx
    @1
    wph
    wps
    vy
    vx
    bj-ralvw.1
    bj-vexw
    a1bi
    albii
    bitr4i
end
