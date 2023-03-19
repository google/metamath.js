include "bicom1.mm"

theorem frege55aid
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) -> ( ps <-> ph ) )

  proof
    wph
    wps
    bicom1
end
