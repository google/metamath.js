include "rp-simp2-frege.mm"
include "3imp.mm"

theorem rp-simp2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) -> ps )

  proof
    wph
    wps
    wch
    wps
    wph
    wps
    wch
    rp-simp2-frege
    3imp
end
