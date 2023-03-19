include "tbw-ax1.mm"

theorem re1luk1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) )

  proof
    wph
    wps
    wch
    tbw-ax1
end
