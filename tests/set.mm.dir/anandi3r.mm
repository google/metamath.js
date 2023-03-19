include "w3a.mm"
include "wa.mm"
include "3anan32.mm"
include "anandir.mm"
include "bitri.mm"

theorem anandi3r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) <-> ( ( ph /\ ps ) /\ ( ch /\ ps ) ) )

  proof
    wph
    wps
    wch
    w3a
    wph
    wch
    wa
    wps
    wa
    wph
    wps
    wa
    wch
    wps
    wa
    wa
    wph
    wps
    wch
    3anan32
    wph
    wch
    wps
    anandir
    bitri
end
