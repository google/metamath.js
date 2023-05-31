include "wi.mm"
include "id.mm"
include "jaao.mm"

theorem pm3.44
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch


  assert |- ( ( ( ps -> ph ) /\ ( ch -> ph ) ) -> ( ( ps \/ ch ) -> ph ) )

  proof
    wps
    wph
    wi
    #
    wps
    wph
    wch
    wph
    wi
    #
    wch
    @0
    id
    @1
    id
    jaao
end
