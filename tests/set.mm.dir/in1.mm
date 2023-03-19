include "wvd1.mm"
include "wi.mm"
include "df-vd1.mm"
include "mpbi.mm"

theorem in1
  let wph: wff ph
  let wps: wff ps
  assume in1.1: |- (. ph ->. ps ).


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wvd1
    wph
    wps
    wi
    in1.1
    wph
    wps
    df-vd1
    mpbi
end
