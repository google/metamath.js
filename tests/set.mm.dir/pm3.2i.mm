include "wa.mm"
include "pm3.2.mm"
include "mp2.mm"

theorem pm3.2i
  let wph: wff ph
  let wps: wff ps
  assume pm3.2i.1: |- ph
  assume pm3.2i.2: |- ps


  assert |- ( ph /\ ps )

  proof
    wph
    wps
    wph
    wps
    wa
    pm3.2i.1
    pm3.2i.2
    wph
    wps
    pm3.2
    mp2
end
