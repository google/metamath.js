include "wa.mm"
include "aistia.mm"
include "pm3.2i.mm"
include "bitru.mm"

theorem astbstanbst
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume astbstanbst.1: |- ( ph <-> T. )
  assume astbstanbst.2: |- ( ps <-> T. )


  assert |- ( ( ph /\ ps ) <-> T. )

  proof
    wph
    wps
    wa
    wph
    wps
    wph
    astbstanbst.1
    aistia
    wps
    astbstanbst.2
    aistia
    pm3.2i
    bitru
end
