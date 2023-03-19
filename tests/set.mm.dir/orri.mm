include "wo.mm"
include "wn.mm"
include "wi.mm"
include "df-or.mm"
include "mpbir.mm"

theorem orri
  param wph: wff ph
  param wps: wff ps
  assume orri.1: |- ( -. ph -> ps )


  assert |- ( ph \/ ps )

  proof
    wph
    wps
    wo
    wph
    wn
    wps
    wi
    orri.1
    wph
    wps
    df-or
    mpbir
end
