include "wa.mm"
include "w3a.mm"
include "wi.mm"
include "3anass.mm"
include "anabs5.mm"
include "bitri.mm"
include "ancom.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "imbi1i.mm"
include "mpbi.mm"

theorem uun2221
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume uun2221.1: |- ( ( ph /\ ph /\ ( ps /\ ph ) ) -> ch )


  assert |- ( ( ps /\ ph ) -> ch )

  proof
    wph
    wph
    wps
    wph
    wa
    #
    w3a
    #
    wch
    wi
    @0
    wch
    wi
    uun2221.1
    @1
    @0
    wch
    @1
    wph
    wph
    wps
    wa
    #
    wa
    #
    @0
    @1
    wph
    @0
    wa
    #
    @3
    @1
    wph
    @4
    wa
    @4
    wph
    wph
    @0
    3anass
    wph
    @0
    anabs5
    bitri
    @2
    @0
    wph
    wph
    wps
    ancom
    #
    anbi2i
    bitr4i
    @3
    @2
    @0
    wph
    wps
    anabs5
    @5
    bitri
    bitri
    imbi1i
    mpbi
end
