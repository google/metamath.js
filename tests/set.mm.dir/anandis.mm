include "wa.mm"
include "an4s.mm"
include "anabsan.mm"

theorem anandis
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta
  assume anandis.1: |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) ) -> ta )


  assert |- ( ( ph /\ ( ps /\ ch ) ) -> ta )

  proof
    wph
    wps
    wch
    wa
    wta
    wph
    wps
    wph
    wch
    wta
    anandis.1
    an4s
    anabsan
end
