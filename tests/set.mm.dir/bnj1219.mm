include "simp2bi.mm"
include "bnj835.mm"

theorem bnj1219
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume bnj1219.1: |- ( ch <-> ( ph /\ ps /\ ze ) )
  assume bnj1219.2: |- ( th <-> ( ch /\ ta /\ et ) )


  assert |- ( th -> ps )

  proof
    wch
    wta
    wet
    wps
    wth
    bnj1219.2
    wch
    wph
    wps
    wze
    bnj1219.1
    simp2bi
    bnj835
end
