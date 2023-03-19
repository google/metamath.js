include "aistia.mm"
include "aisfina.mm"
include "abnotbtaxb.mm"

theorem aistbisfiaxb
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume aistbisfiaxb.1: |- ( ph <-> T. )
  assume aistbisfiaxb.2: |- ( ps <-> F. )


  assert |- ( ph \/_ ps )

  proof
    wph
    wps
    wph
    aistbisfiaxb.1
    aistia
    wps
    aistbisfiaxb.2
    aisfina
    abnotbtaxb
end
