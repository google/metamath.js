include "w3a.mm"
include "wa.mm"
include "pm3.2i.mm"
include "df-3an.mm"
include "mpbir2an.mm"

theorem 3pm3.2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume 3pm3.2i.1: |- ph
  assume 3pm3.2i.2: |- ps
  assume 3pm3.2i.3: |- ch


  assert |- ( ph /\ ps /\ ch )

  proof
    wph
    wps
    wch
    w3a
    wph
    wps
    wa
    wch
    wph
    wps
    3pm3.2i.1
    3pm3.2i.2
    pm3.2i
    3pm3.2i.3
    wph
    wps
    wch
    df-3an
    mpbir2an
end
