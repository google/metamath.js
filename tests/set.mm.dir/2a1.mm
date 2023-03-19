include "id.mm"
include "2a1d.mm"

theorem 2a1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ph -> ( ps -> ( ch -> ph ) ) )

  proof
    wph
    wph
    wps
    wch
    wph
    id
    2a1d
end
