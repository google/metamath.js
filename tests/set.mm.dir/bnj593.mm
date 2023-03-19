include "wex.mm"
include "eximi.mm"
include "syl.mm"

theorem bnj593
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bnj593.1: |- ( ph -> E. x ps )
  assume bnj593.2: |- ( ps -> ch )


  assert |- ( ph -> E. x ch )

  proof
    wph
    wps
    vx
    wex
    wch
    vx
    wex
    bnj593.1
    wps
    wch
    vx
    bnj593.2
    eximi
    syl
end
