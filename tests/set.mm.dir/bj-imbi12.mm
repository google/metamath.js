include "wb.mm"
include "wi.mm"
include "imbi12.mm"
include "imp.mm"

theorem bj-imbi12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph <-> ps ) /\ ( ch <-> th ) ) -> ( ( ph -> ch ) <-> ( ps -> th ) ) )

  proof
    wph
    wps
    wb
    wch
    wth
    wb
    wph
    wch
    wi
    wps
    wth
    wi
    wb
    wph
    wps
    wch
    wth
    imbi12
    imp
end
