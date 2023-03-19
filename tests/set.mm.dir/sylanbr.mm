include "biimpri.mm"
include "sylan.mm"

theorem sylanbr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume sylanbr.1: |- ( ps <-> ph )
  assume sylanbr.2: |- ( ( ps /\ ch ) -> th )


  assert |- ( ( ph /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    wps
    wph
    sylanbr.1
    biimpri
    sylanbr.2
    sylan
end
