include "cab.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "hbab1.mm"
include "cleqh.mm"
include "abid.mm"
include "bibi12i.mm"
include "albii.mm"
include "bitr2i.mm"

theorem abbi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ( ph <-> ps ) <-> { x | ph } = { x | ps } )

  proof
    wph
    vx
    cab
    #
    wps
    vx
    cab
    #
    wceq
    vx
    cv
    #
    @0
    wcel
    #
    @2
    @1
    wcel
    #
    wb
    #
    vx
    wal
    wph
    wps
    wb
    #
    vx
    wal
    vx
    vy
    @0
    @1
    wph
    vx
    vy
    hbab1
    wps
    vx
    vy
    hbab1
    cleqh
    @5
    @6
    vx
    @3
    wph
    @4
    wps
    wph
    vx
    abid
    wps
    vx
    abid
    bibi12i
    albii
    bitr2i
end
