include "wnf.mm"
include "a1i.mm"
include "alrimdd.mm"

theorem alrimd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume alrimd.1: |- F/ x ph
  assume alrimd.2: |- F/ x ps
  assume alrimd.3: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ps -> A. x ch ) )

  proof
    wph
    wps
    wch
    vx
    alrimd.1
    wps
    vx
    wnf
    wph
    alrimd.2
    a1i
    alrimd.3
    alrimdd
end
