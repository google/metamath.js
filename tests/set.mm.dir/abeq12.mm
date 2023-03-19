include "wb.mm"
include "wal.mm"
include "cab.mm"
include "wceq.mm"
include "abbi.mm"
include "biimpi.mm"

theorem abeq12
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ph <-> ps ) -> { x | ph } = { x | ps } )

  proof
    wph
    wps
    wb
    vx
    wal
    wph
    vx
    cab
    wps
    vx
    cab
    wceq
    wph
    wps
    vx
    abbi
    biimpi
end
