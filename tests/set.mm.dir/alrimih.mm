include "sylg.mm"

theorem alrimih
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume alrimih.1: |- ( ph -> A. x ph )
  assume alrimih.2: |- ( ph -> ps )


  assert |- ( ph -> A. x ps )

  proof
    wph
    wph
    wps
    vx
    alrimih.1
    alrimih.2
    sylg
end
