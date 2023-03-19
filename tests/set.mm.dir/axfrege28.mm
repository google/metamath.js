include "con3.mm"

theorem axfrege28
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) )

  proof
    wph
    wps
    con3
end
