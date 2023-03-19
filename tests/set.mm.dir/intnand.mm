include "wa.mm"
include "simpr.mm"
include "nsyl.mm"

theorem intnand
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume intnand.1: |- ( ph -> -. ps )


  assert |- ( ph -> -. ( ch /\ ps ) )

  proof
    wph
    wps
    wch
    wps
    wa
    intnand.1
    wch
    wps
    simpr
    nsyl
end
