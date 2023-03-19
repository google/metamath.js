include "wi.mm"
include "a1i.mm"

theorem 2a1i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume 2a1i.1: |- ph


  assert |- ( ps -> ( ch -> ph ) )

  proof
    wch
    wph
    wi
    wps
    wph
    wch
    2a1i.1
    a1i
    a1i
end
