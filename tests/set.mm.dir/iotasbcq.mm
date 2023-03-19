include "wb.mm"
include "wal.mm"
include "cio.mm"
include "iotabi.mm"
include "sbceq1d.mm"

theorem iotasbcq
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ( ph <-> ps ) -> ( [. ( iota x ph ) / y ]. ch <-> [. ( iota x ps ) / y ]. ch ) )

  proof
    wph
    wps
    wb
    vx
    wal
    wch
    vy
    wph
    vx
    cio
    wps
    vx
    cio
    wph
    wps
    vx
    iotabi
    sbceq1d
end
