include "wo.mm"
include "wn.mm"
include "wi.mm"
include "df-or.mm"
include "mpbi.mm"

theorem ori
  let wph: wff ph
  let wps: wff ps
  assume ori.1: |- ( ph \/ ps )


  assert |- ( -. ph -> ps )

  proof
    wph
    wps
    wo
    wph
    wn
    wps
    wi
    ori.1
    wph
    wps
    df-or
    mpbi
end
