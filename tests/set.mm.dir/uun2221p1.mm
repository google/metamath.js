include "wa.mm"
include "w3a.mm"
include "wi.mm"
include "3anrot.mm"
include "imbi1i.mm"
include "mpbir.mm"
include "3anass.mm"
include "anabs5.mm"
include "bitri.mm"
include "ancom.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "mpbi.mm"

theorem uun2221p1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume uun2221p1.1: |- ( ( ph /\ ( ps /\ ph ) /\ ph ) -> ch )


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
    #
    @0
    wch
    wi
    @2
    wph
    @0
    wph
    w3a
    #
    wch
    wi
    uun2221p1.1
    @1
    @3
    wch
    wph
    wph
    @0
    3anrot
    imbi1i
    mpbir
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
    @5
    @1
    wph
    @6
    wa
    @6
    wph
    wph
    @0
    3anass
    wph
    @0
    anabs5
    bitri
    @4
    @0
    wph
    wph
    wps
    ancom
    #
    anbi2i
    bitr4i
    @5
    @4
    @0
    wph
    wps
    anabs5
    @7
    bitri
    bitri
    imbi1i
    mpbi
end
