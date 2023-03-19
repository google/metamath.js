include "cv.mm"
include "wceq.mm"
include "copab.mm"
include "eqid.mm"
include "wb.mm"
include "a1i.mm"
include "opabbidv.mm"
include "ax-mp.mm"

theorem opabbii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume opabbii.1: |- ( ph <-> ps )


  assert |- { <. x , y >. | ph } = { <. x , y >. | ps }

  proof
    vz
    cv
    #
    @0
    wceq
    #
    wph
    vx
    vy
    copab
    wps
    vx
    vy
    copab
    wceq
    @0
    eqid
    @1
    wph
    wps
    vx
    vy
    wph
    wps
    wb
    @1
    opabbii.1
    a1i
    opabbidv
    ax-mp
end
