include "w3o.mm"
include "3mix1.mm"
include "3orrot.mm"
include "sylib.mm"

theorem 3mix3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ph -> ( ps \/ ch \/ ph ) )

  proof
    wph
    wph
    wps
    wch
    w3o
    wps
    wch
    wph
    w3o
    wph
    wps
    wch
    3mix1
    wph
    wps
    wch
    3orrot
    sylib
end
