include "wi.mm"
include "exp32.mm"
include "imp.mm"

theorem expr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume expr.1: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ( ph /\ ps ) -> ( ch -> th ) )

  proof
    wph
    wps
    wch
    wth
    wi
    wph
    wps
    wch
    wth
    expr.1
    exp32
    imp
end
