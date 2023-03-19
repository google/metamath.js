include "wa.mm"
include "ancom.mm"
include "sylbir.mm"
include "3impdir.mm"

theorem 3impdirp1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3impdirp1.1: |- ( ( ( ch /\ ps ) /\ ( ph /\ ps ) ) -> th )


  assert |- ( ( ph /\ ch /\ ps ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wa
    #
    wch
    wps
    wa
    #
    wa
    @1
    @0
    wa
    wth
    @1
    @0
    ancom
    3impdirp1.1
    sylbir
    3impdir
end
