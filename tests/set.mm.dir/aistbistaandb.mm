include "aistia.mm"
include "pm3.2i.mm"

theorem aistbistaandb
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume aistbistaandb.1: |- ( ph <-> T. )
  assume aistbistaandb.2: |- ( ps <-> T. )


  assert |- ( ph /\ ps )

  proof
    wph
    wps
    wph
    aistbistaandb.1
    aistia
    wps
    aistbistaandb.2
    aistia
    pm3.2i
end
