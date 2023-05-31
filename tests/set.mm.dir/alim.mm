include "ax-4.mm"

theorem alim
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x


  assert |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) )

  proof
    wph
    wps
    vx
    ax-4
end
