include "ax-5.mm"
include "alrimih.mm"

theorem alrimiv
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  assume alrimiv.1: |- ( ph -> ps )

  disjoint ph x
  assert |- ( ph -> A. x ps )

  proof
    wph
    wps
    vx
    wph
    vx
    ax-5
    alrimiv.1
    alrimih
end
