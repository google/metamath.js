include "wfal.mm"
include "wb.mm"
include "wn.mm"
include "nbfal.mm"
include "bibi2i.mm"
include "pm5.19.mm"
include "pm2.21i.mm"
include "sylbir.mm"

theorem bisym1
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ps <-> ( ps <-> F. ) ) -> ( ps <-> ph ) )

  proof
    wps
    wps
    wfal
    wb
    #
    wb
    wps
    wps
    wn
    #
    wb
    #
    wps
    wph
    wb
    #
    @1
    @0
    wps
    wps
    nbfal
    bibi2i
    @2
    @3
    wps
    pm5.19
    pm2.21i
    sylbir
end
