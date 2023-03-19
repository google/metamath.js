include "imim1.mm"

theorem tbw-ax1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) )

  proof
    wph
    wps
    wch
    imim1
end
