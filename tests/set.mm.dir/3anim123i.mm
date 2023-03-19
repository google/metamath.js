include "w3a.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "3jca.mm"

theorem 3anim123i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume 3anim123i.1: |- ( ph -> ps )
  assume 3anim123i.2: |- ( ch -> th )
  assume 3anim123i.3: |- ( ta -> et )


  assert |- ( ( ph /\ ch /\ ta ) -> ( ps /\ th /\ et ) )

  proof
    wph
    wch
    wta
    w3a
    wps
    wth
    wet
    wph
    wch
    wps
    wta
    3anim123i.1
    3ad2ant1
    wch
    wph
    wth
    wta
    3anim123i.2
    3ad2ant2
    wta
    wph
    wet
    wch
    3anim123i.3
    3ad2ant3
    3jca
end
