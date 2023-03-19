include "wb.mm"
include "wif.mm"
include "wi.mm"
include "ax-frege52a.mm"
include "ax-frege8.mm"
include "ax-mp.mm"

theorem frege53a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( if- ( ph , th , ch ) -> ( ( ph <-> ps ) -> if- ( ps , th , ch ) ) )

  proof
    wph
    wps
    wb
    #
    wph
    wth
    wch
    wif
    #
    wps
    wth
    wch
    wif
    #
    wi
    wi
    @1
    @0
    @2
    wi
    wi
    wph
    wps
    wch
    wth
    ax-frege52a
    @0
    @1
    @2
    ax-frege8
    ax-mp
end
