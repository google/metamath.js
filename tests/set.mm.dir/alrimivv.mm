include "wal.mm"
include "alrimiv.mm"

theorem alrimivv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume alrimivv.1: |- ( ph -> ps )

  disjoint ph x
  disjoint ph y
  assert |- ( ph -> A. x A. y ps )

  proof
    wph
    wps
    vy
    wal
    vx
    wph
    wps
    vy
    alrimivv.1
    alrimiv
    alrimiv
end
