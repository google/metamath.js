include "wnan.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "wl-dfnan2.mm"
include "nanan.mm"
include "imbi2i.mm"
include "bitr4i.mm"

theorem wl-nannan
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -/\ ( ps -/\ ch ) ) <-> ( ph -> ( ps /\ ch ) ) )

  proof
    wph
    wps
    wch
    wnan
    #
    wnan
    wph
    @0
    wn
    #
    wi
    wph
    wps
    wch
    wa
    #
    wi
    wph
    @0
    wl-dfnan2
    @2
    @1
    wph
    wps
    wch
    nanan
    imbi2i
    bitr4i
end
