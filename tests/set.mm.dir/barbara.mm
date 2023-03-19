include "wi.mm"
include "wal.mm"
include "alsyl.mm"
include "mp2an.mm"

theorem barbara
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume barbara.maj: |- A. x ( ph -> ps )
  assume barbara.min: |- A. x ( ch -> ph )


  assert |- A. x ( ch -> ps )

  proof
    wch
    wph
    wi
    vx
    wal
    wph
    wps
    wi
    vx
    wal
    wch
    wps
    wi
    vx
    wal
    barbara.min
    barbara.maj
    wch
    wph
    wps
    vx
    alsyl
    mp2an
end
