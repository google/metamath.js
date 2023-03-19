include "wal.mm"
include "hba1-o.mm"
include "alrimih.mm"

theorem axc4i-o
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume axc4i-o.1: |- ( A. x ph -> ps )


  assert |- ( A. x ph -> A. x ps )

  proof
    wph
    vx
    wal
    wps
    vx
    wph
    vx
    hba1-o
    axc4i-o.1
    alrimih
end
