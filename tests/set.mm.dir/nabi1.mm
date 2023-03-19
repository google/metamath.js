include "nanbi1.mm"

theorem nabi1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph <-> ps ) -> ( ( ph -/\ ch ) <-> ( ps -/\ ch ) ) )

  proof
    wph
    wps
    wch
    nanbi1
end
