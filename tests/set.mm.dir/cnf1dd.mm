include "wn.mm"
include "wo.mm"
include "wa.mm"
include "jcad.mm"
include "wi.mm"
include "df-or.mm"
include "pm3.35.mm"
include "sylan2b.mm"
include "syl6.mm"

theorem cnf1dd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume cnf1dd.1: |- ( ph -> ( ps -> -. ch ) )
  assume cnf1dd.2: |- ( ph -> ( ps -> ( ch \/ th ) ) )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wn
    #
    wch
    wth
    wo
    #
    wa
    wth
    wph
    wps
    @0
    @1
    cnf1dd.1
    cnf1dd.2
    jcad
    @1
    @0
    @0
    wth
    wi
    wth
    wch
    wth
    df-or
    @0
    wth
    pm3.35
    sylan2b
    syl6
end
