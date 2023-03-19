include "wo.mm"
include "orcd.mm"
include "olcd.mm"
include "jaoi.mm"

theorem orim12i
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume orim12i.1: |- ( ph -> ps )
  assume orim12i.2: |- ( ch -> th )


  assert |- ( ( ph \/ ch ) -> ( ps \/ th ) )

  proof
    wph
    wps
    wth
    wo
    wch
    wph
    wps
    wth
    orim12i.1
    orcd
    wch
    wth
    wps
    orim12i.2
    olcd
    jaoi
end
