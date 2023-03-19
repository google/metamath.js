include "w3o.mm"
include "wi.mm"
include "w3a.mm"
include "3mix1.mm"
include "imim1i.mm"
include "3mix2.mm"
include "3mix3.mm"
include "3jca.mm"
include "3jao.mm"
include "impbii.mm"

theorem 3jaob
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph \/ ch \/ th ) -> ps ) <-> ( ( ph -> ps ) /\ ( ch -> ps ) /\ ( th -> ps ) ) )

  proof
    wph
    wch
    wth
    w3o
    #
    wps
    wi
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
    @1
    @2
    @3
    @4
    wph
    @0
    wps
    wph
    wch
    wth
    3mix1
    imim1i
    wch
    @0
    wps
    wch
    wph
    wth
    3mix2
    imim1i
    wth
    @0
    wps
    wth
    wph
    wch
    3mix3
    imim1i
    3jca
    wph
    wps
    wch
    wth
    3jao
    impbii
end
