include "ax-4.mm"

theorem alim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) )

  proof
    wph
    wps
    vx
    ax-4
end
