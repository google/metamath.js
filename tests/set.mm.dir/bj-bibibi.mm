include "wb.mm"
include "pm5.501.mm"
include "bianir.mm"
include "ex.mm"
include "wn.mm"
include "bibif.mm"
include "con2bid.mm"
include "biimprd.mm"
include "bija.mm"
include "impbii.mm"

theorem bj-bibibi
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph <-> ( ps <-> ( ph <-> ps ) ) )

  proof
    wph
    wps
    wph
    wps
    wb
    #
    wb
    wph
    wps
    pm5.501
    wps
    @0
    wph
    wps
    @0
    wph
    wps
    wph
    bianir
    ex
    wps
    wn
    #
    wph
    @0
    wn
    @1
    @0
    wph
    wph
    wps
    bibif
    con2bid
    biimprd
    bija
    impbii
end
