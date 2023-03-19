include "wi.mm"
include "wa.mm"
include "wb.mm"
include "simpr.mm"
include "ancr.mm"
include "impbid2.mm"
include "bibi2d.mm"
include "biimpa.mm"

theorem bimsc1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph -> ps ) /\ ( ch <-> ( ps /\ ph ) ) ) -> ( ch <-> ph ) )

  proof
    wph
    wps
    wi
    #
    wch
    wps
    wph
    wa
    #
    wb
    wch
    wph
    wb
    @0
    @1
    wph
    wch
    @0
    @1
    wph
    wps
    wph
    simpr
    wph
    wps
    ancr
    impbid2
    bibi2d
    biimpa
end
