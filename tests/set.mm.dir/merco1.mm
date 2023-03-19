include "wi.mm"
include "wfal.mm"
include "wn.mm"
include "ax-1.mm"
include "falim.mm"
include "ja.mm"
include "imim2i.mm"
include "imim1i.mm"
include "meredith.mm"
include "syl.mm"

theorem merco1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ( ( ph -> ps ) -> ( ch -> F. ) ) -> th ) -> ta ) -> ( ( ta -> ph ) -> ( ch -> ph ) ) )

  proof
    wph
    wps
    wi
    #
    wch
    wfal
    wi
    #
    wi
    #
    wth
    wi
    #
    wta
    wi
    @0
    wth
    wn
    #
    wch
    wn
    #
    wi
    #
    wi
    #
    wth
    wi
    #
    wta
    wi
    wta
    wph
    wi
    wch
    wph
    wi
    wi
    @8
    @3
    wta
    @2
    @7
    wth
    @1
    @6
    @0
    wch
    wfal
    @6
    @5
    @4
    ax-1
    @6
    falim
    ja
    imim2i
    imim1i
    imim1i
    wph
    wps
    wth
    wch
    wta
    meredith
    syl
end
