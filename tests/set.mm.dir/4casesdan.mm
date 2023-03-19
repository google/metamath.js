include "wi.mm"
include "wa.mm"
include "expcom.mm"
include "wn.mm"
include "4cases.mm"

theorem 4casesdan
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 4casesdan.1: |- ( ( ph /\ ( ps /\ ch ) ) -> th )
  assume 4casesdan.2: |- ( ( ph /\ ( ps /\ -. ch ) ) -> th )
  assume 4casesdan.3: |- ( ( ph /\ ( -. ps /\ ch ) ) -> th )
  assume 4casesdan.4: |- ( ( ph /\ ( -. ps /\ -. ch ) ) -> th )


  assert |- ( ph -> th )

  proof
    wps
    wch
    wph
    wth
    wi
    wph
    wps
    wch
    wa
    wth
    4casesdan.1
    expcom
    wph
    wps
    wch
    wn
    #
    wa
    wth
    4casesdan.2
    expcom
    wph
    wps
    wn
    #
    wch
    wa
    wth
    4casesdan.3
    expcom
    wph
    @1
    @0
    wa
    wth
    4casesdan.4
    expcom
    4cases
end
