include "cv.mm"
include "wcel.mm"
include "bnj1196.mm"
include "bnj1345.mm"

theorem bnj1521
  let wph: wff ph
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let cB: class B
  assume bnj1521.1: |- ( ch -> E. x e. B ph )
  assume bnj1521.2: |- ( th <-> ( ch /\ x e. B /\ ph ) )
  assume bnj1521.3: |- ( ch -> A. x ch )


  assert |- ( ch -> E. x th )

  proof
    wch
    vx
    cv
    cB
    wcel
    wph
    wth
    vx
    wch
    wph
    vx
    cB
    bnj1521.1
    bnj1196
    bnj1521.2
    bnj1521.3
    bnj1345
end
