include "wi.mm"
include "wb.mm"
include "impbi.mm"
include "bj-bi3ant.mm"

theorem bj-bisym
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph -> ps ) -> ( ch -> th ) ) -> ( ( ( ps -> ph ) -> ( th -> ch ) ) -> ( ( ph <-> ps ) -> ( ch <-> th ) ) ) )

  proof
    wch
    wth
    wi
    wth
    wch
    wi
    wch
    wth
    wb
    wph
    wps
    wch
    wth
    impbi
    bj-bi3ant
end
