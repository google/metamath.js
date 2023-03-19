include "wo.mm"
include "wa.mm"
include "wi.mm"
include "com12.mm"
include "ccase.mm"

theorem ccased
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ccased.1: |- ( ph -> ( ( ps /\ ch ) -> et ) )
  assume ccased.2: |- ( ph -> ( ( th /\ ch ) -> et ) )
  assume ccased.3: |- ( ph -> ( ( ps /\ ta ) -> et ) )
  assume ccased.4: |- ( ph -> ( ( th /\ ta ) -> et ) )


  assert |- ( ph -> ( ( ( ps \/ th ) /\ ( ch \/ ta ) ) -> et ) )

  proof
    wps
    wth
    wo
    wch
    wta
    wo
    wa
    wph
    wet
    wps
    wch
    wth
    wta
    wph
    wet
    wi
    wph
    wps
    wch
    wa
    wet
    ccased.1
    com12
    wph
    wth
    wch
    wa
    wet
    ccased.2
    com12
    wph
    wps
    wta
    wa
    wet
    ccased.3
    com12
    wph
    wth
    wta
    wa
    wet
    ccased.4
    com12
    ccase
    com12
end
