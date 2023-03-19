include "wvd1.mm"
include "wi.mm"
include "df-vd1.mm"
include "mpbir.mm"

theorem dfvd1ir
  let wph: wff ph
  let wps: wff ps
  assume dfvd1ir.1: |- ( ph -> ps )


  assert |- (. ph ->. ps ).

  proof
    wph
    wps
    wvd1
    wph
    wps
    wi
    dfvd1ir.1
    wph
    wps
    df-vd1
    mpbir
end
