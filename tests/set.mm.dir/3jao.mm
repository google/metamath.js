include "w3o.mm"
include "wo.mm"
include "wi.mm"
include "w3a.mm"
include "df-3or.mm"
include "jao.mm"
include "syl6.mm"
include "3imp.mm"
include "syl5bi.mm"

theorem 3jao
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph -> ps ) /\ ( ch -> ps ) /\ ( th -> ps ) ) -> ( ( ph \/ ch \/ th ) -> ps ) )

  proof
    wph
    wch
    wth
    w3o
    wph
    wch
    wo
    #
    wth
    wo
    #
    wph
    wps
    wi
    #
    wch
    wps
    wi
    #
    wth
    wps
    wi
    #
    w3a
    wps
    wph
    wch
    wth
    df-3or
    @2
    @3
    @4
    @1
    wps
    wi
    #
    @2
    @3
    @0
    wps
    wi
    @4
    @5
    wi
    wph
    wps
    wch
    jao
    @0
    wps
    wth
    jao
    syl6
    3imp
    syl5bi
end
