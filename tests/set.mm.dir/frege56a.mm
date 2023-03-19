include "wb.mm"
include "wi.mm"
include "wif.mm"
include "frege55cor1a.mm"
include "frege9.mm"
include "ax-mp.mm"

theorem frege56a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph <-> ps ) -> ( if- ( ph , ch , th ) -> if- ( ps , ch , th ) ) ) -> ( ( ps <-> ph ) -> ( if- ( ph , ch , th ) -> if- ( ps , ch , th ) ) ) )

  proof
    wps
    wph
    wb
    #
    wph
    wps
    wb
    #
    wi
    @1
    wph
    wch
    wth
    wif
    wps
    wch
    wth
    wif
    wi
    #
    wi
    @0
    @2
    wi
    wi
    wps
    wph
    frege55cor1a
    @0
    @1
    @2
    frege9
    ax-mp
end
