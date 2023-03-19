include "wb.mm"
include "wssb.mm"
include "bj-ssbbi.mm"
include "mpg.mm"

theorem bj-ssbbii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vt: setvar t
  assume bj-ssbbii.1: |- ( ph <-> ps )


  assert |- ( [b t /b x ]b ph <-> [b t /b x ]b ps )

  proof
    wph
    wps
    wb
    wph
    vx
    vt
    wssb
    wps
    vx
    vt
    wssb
    wb
    vx
    wph
    wps
    vx
    vt
    bj-ssbbi
    bj-ssbbii.1
    mpg
end
