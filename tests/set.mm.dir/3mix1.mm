include "wo.mm"
include "w3o.mm"
include "orc.mm"
include "3orass.mm"
include "sylibr.mm"

theorem 3mix1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ph -> ( ph \/ ps \/ ch ) )

  proof
    wph
    wph
    wps
    wch
    wo
    #
    wo
    wph
    wps
    wch
    w3o
    wph
    @0
    orc
    wph
    wps
    wch
    3orass
    sylibr
end
