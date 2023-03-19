include "cv.mm"
include "wceq.mm"
include "coprab.mm"
include "eqid.mm"
include "wb.mm"
include "a1i.mm"
include "oprabbidv.mm"
include "ax-mp.mm"

theorem oprabbii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume oprabbii.1: |- ( ph <-> ps )

  disjoint x z
  disjoint y z
  disjoint w x
  disjoint w z
  disjoint w y
  disjoint ph w
  disjoint ps w
  assert |- { <. <. x , y >. , z >. | ph } = { <. <. x , y >. , z >. | ps }

  proof
    vw
    cv
    #
    @0
    wceq
    #
    wph
    vx
    vy
    vz
    coprab
    wps
    vx
    vy
    vz
    coprab
    wceq
    @0
    eqid
    @1
    wph
    wps
    vx
    vy
    vz
    wph
    wps
    wb
    @1
    oprabbii.1
    a1i
    oprabbidv
    ax-mp
end
