include "w3o.mm"
include "wo.mm"
include "wn.mm"
include "3orass.mm"
include "orel1.mm"
include "syl5bi.mm"

theorem 3orel1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( -. ph -> ( ( ph \/ ps \/ ch ) -> ( ps \/ ch ) ) )

  proof
    wph
    wps
    wch
    w3o
    wph
    wps
    wch
    wo
    #
    wo
    wph
    wn
    @0
    wph
    wps
    wch
    3orass
    wph
    @0
    orel1
    syl5bi
end
