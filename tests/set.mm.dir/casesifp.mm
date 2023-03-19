include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wif.mm"
include "cases.mm"
include "df-ifp.mm"
include "bitr4i.mm"

theorem casesifp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume casesifp.1: |- ( ph -> ( ps <-> ch ) )
  assume casesifp.2: |- ( -. ph -> ( ps <-> th ) )


  assert |- ( ps <-> if- ( ph , ch , th ) )

  proof
    wps
    wph
    wch
    wa
    wph
    wn
    wth
    wa
    wo
    wph
    wch
    wth
    wif
    wph
    wps
    wch
    wth
    casesifp.1
    casesifp.2
    cases
    wph
    wch
    wth
    df-ifp
    bitr4i
end
