include "whad.mm"
include "wb.mm"
include "wxo.mm"
include "had1.mm"
include "had0.mm"
include "casesifp.mm"

theorem hadifp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( hadd ( ph , ps , ch ) <-> if- ( ph , ( ps <-> ch ) , ( ps \/_ ch ) ) )

  proof
    wph
    wph
    wps
    wch
    whad
    wps
    wch
    wb
    wps
    wch
    wxo
    wph
    wps
    wch
    had1
    wph
    wps
    wch
    had0
    casesifp
end
