include "syld.mm"
include "jcad.mm"

theorem ex-natded5.3-2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ex-natded5.3.1: |- ( ph -> ( ps -> ch ) )
  assume ex-natded5.3.2: |- ( ph -> ( ch -> th ) )


  assert |- ( ph -> ( ps -> ( ch /\ th ) ) )

  proof
    wph
    wps
    wch
    wth
    ex-natded5.3.1
    wph
    wps
    wch
    wth
    ex-natded5.3.1
    ex-natded5.3.2
    syld
    jcad
end
