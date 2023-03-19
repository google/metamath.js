include "aisfina.mm"
include "aistia.mm"
include "abnotataxb.mm"

theorem aisfbistiaxb
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume aisfbistiaxb.1: |- ( ph <-> F. )
  assume aisfbistiaxb.2: |- ( ps <-> T. )


  assert |- ( ph \/_ ps )

  proof
    wph
    wps
    wph
    aisfbistiaxb.1
    aisfina
    wps
    aisfbistiaxb.2
    aistia
    abnotataxb
end
