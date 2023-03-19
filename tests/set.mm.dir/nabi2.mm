include "nanbi2.mm"

theorem nabi2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph <-> ps ) -> ( ( ch -/\ ph ) <-> ( ch -/\ ps ) ) )

  proof
    wph
    wps
    wch
    nanbi2
end
