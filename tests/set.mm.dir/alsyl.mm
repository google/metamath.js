include "wi.mm"
include "pm3.33.mm"
include "alanimi.mm"

theorem alsyl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x


  assert |- ( ( A. x ( ph -> ps ) /\ A. x ( ps -> ch ) ) -> A. x ( ph -> ch ) )

  proof
    wph
    wps
    wi
    wps
    wch
    wi
    wph
    wch
    wi
    vx
    wph
    wps
    wch
    pm3.33
    alanimi
end
