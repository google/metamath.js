include "wnan.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "imnan.mm"
include "nanan.mm"
include "imbi2i.mm"
include "df-nan.mm"
include "3bitr4ri.mm"

theorem nannan
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -/\ ( ch -/\ ps ) ) <-> ( ph -> ( ch /\ ps ) ) )

  proof
    wph
    wch
    wps
    wnan
    #
    wn
    #
    wi
    wph
    @0
    wa
    wn
    wph
    wch
    wps
    wa
    #
    wi
    wph
    @0
    wnan
    wph
    @0
    imnan
    @2
    @1
    wph
    wch
    wps
    nanan
    imbi2i
    wph
    @0
    df-nan
    3bitr4ri
end
