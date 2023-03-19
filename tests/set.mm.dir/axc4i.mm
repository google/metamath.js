include "wal.mm"
include "nfa1.mm"
include "alrimi.mm"

theorem axc4i
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  assume axc4i.1: |- ( A. x ph -> ps )


  assert |- ( A. x ph -> A. x ps )

  proof
    wph
    vx
    wal
    wps
    vx
    wph
    vx
    nfa1
    axc4i.1
    alrimi
end
