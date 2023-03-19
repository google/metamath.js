include "wfal.mm"
include "wnan.mm"
include "wa.mm"
include "wn.mm"
include "df-nan.mm"
include "biimpi.mm"
include "anbi2i.mm"
include "sylnib.mm"
include "simpl.mm"
include "fal.mm"
include "intnan.mm"
include "jctir.mm"
include "nsyl.mm"
include "sylibr.mm"

theorem nandsym1
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ps -/\ ( ps -/\ F. ) ) -> ( ps -/\ ph ) )

  proof
    wps
    wps
    wfal
    wnan
    #
    wnan
    #
    wps
    wph
    wa
    #
    wn
    wps
    wph
    wnan
    @1
    wps
    wps
    wfal
    wa
    wn
    #
    wa
    #
    @2
    @1
    wps
    @0
    wa
    #
    @4
    @1
    @5
    wn
    wps
    @0
    df-nan
    biimpi
    @0
    @3
    wps
    wps
    wfal
    df-nan
    anbi2i
    sylnib
    @2
    wps
    @3
    wps
    wph
    simpl
    wfal
    wps
    fal
    intnan
    jctir
    nsyl
    wps
    wph
    df-nan
    sylibr
end
