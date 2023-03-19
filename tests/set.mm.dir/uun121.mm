include "wa.mm"
include "anabs5.mm"
include "sylbir.mm"

theorem uun121
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume uun121.1: |- ( ( ph /\ ( ph /\ ps ) ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wa
    #
    wph
    @0
    wa
    wch
    wph
    wps
    anabs5
    uun121.1
    sylbir
end
