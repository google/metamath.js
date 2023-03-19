include "nf5i.mm"
include "equsal.mm"

theorem equsalh
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume equsalh.1: |- ( ps -> A. x ps )
  assume equsalh.2: |- ( x = y -> ( ph <-> ps ) )


  assert |- ( A. x ( x = y -> ph ) <-> ps )

  proof
    wph
    wps
    vx
    vy
    wps
    vx
    equsalh.1
    nf5i
    equsalh.2
    equsal
end
