include "wb.mm"
include "wif.mm"
include "wi.mm"
include "ax-frege52a.mm"
include "frege56a.mm"
include "ax-mp.mm"

theorem frege57a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph <-> ps ) -> ( if- ( ps , ch , th ) -> if- ( ph , ch , th ) ) )

  proof
    wps
    wph
    wb
    wps
    wch
    wth
    wif
    wph
    wch
    wth
    wif
    wi
    #
    wi
    wph
    wps
    wb
    @0
    wi
    wps
    wph
    wth
    wch
    ax-frege52a
    wps
    wph
    wch
    wth
    frege56a
    ax-mp
end
