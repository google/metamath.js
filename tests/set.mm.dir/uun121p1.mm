include "wa.mm"
include "anabs1.mm"
include "sylbir.mm"

theorem uun121p1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume uun121p1.1: |- ( ( ( ph /\ ps ) /\ ph ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wa
    #
    @0
    wph
    wa
    wch
    wph
    wps
    anabs1
    uun121p1.1
    sylbir
end
