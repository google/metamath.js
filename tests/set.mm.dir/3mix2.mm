include "w3o.mm"
include "3mix1.mm"
include "3orrot.mm"
include "sylibr.mm"

theorem 3mix2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ph -> ( ps \/ ph \/ ch ) )

  proof
    wph
    wph
    wch
    wps
    w3o
    wps
    wph
    wch
    w3o
    wph
    wch
    wps
    3mix1
    wps
    wph
    wch
    3orrot
    sylibr
end
