include "nf5ri.mm"
include "alrimih.mm"

theorem alrimi
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  assume alrimi.1: |- F/ x ph
  assume alrimi.2: |- ( ph -> ps )


  assert |- ( ph -> A. x ps )

  proof
    wph
    wps
    vx
    wph
    vx
    alrimi.1
    nf5ri
    alrimi.2
    alrimih
end
