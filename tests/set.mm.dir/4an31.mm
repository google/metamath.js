include "wa.mm"
include "an31.mm"
include "sylanb.mm"

theorem 4an31
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 4an31.1: |- ( ( ( ( ch /\ ps ) /\ ph ) /\ th ) -> ta )


  assert |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta )

  proof
    wph
    wps
    wa
    wch
    wa
    wch
    wps
    wa
    wph
    wa
    wth
    wta
    wph
    wps
    wch
    an31
    4an31.1
    sylanb
end
