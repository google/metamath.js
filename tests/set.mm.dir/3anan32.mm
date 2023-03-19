include "w3a.mm"
include "wa.mm"
include "df-3an.mm"
include "an32.mm"
include "bitri.mm"

theorem 3anan32
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) <-> ( ( ph /\ ch ) /\ ps ) )

  proof
    wph
    wps
    wch
    w3a
    wph
    wps
    wa
    wch
    wa
    wph
    wch
    wa
    wps
    wa
    wph
    wps
    wch
    df-3an
    wph
    wps
    wch
    an32
    bitri
end
