include "wi.mm"
include "imim1.mm"
include "imim2.mm"
include "syl5.mm"

theorem peirceroll
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ( ph -> ps ) -> ph ) -> ph ) -> ( ( ( ph -> ps ) -> ch ) -> ( ( ch -> ph ) -> ph ) ) )

  proof
    wph
    wps
    wi
    #
    wch
    wi
    wch
    wph
    wi
    #
    @0
    wph
    wi
    #
    wi
    @2
    wph
    wi
    @1
    wph
    wi
    @0
    wch
    wph
    imim1
    @2
    wph
    @1
    imim2
    syl5
end
