include "wi.mm"

theorem bj-0
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert wff ( ( ph -> ps ) -> ch )

  proof
    wph
    wps
    wi
    wch
    wi
end
