include "wal.mm"
include "a1i.mm"

theorem sptruw
  let wph: wff ph
  let vx: setvar x
  assume sptruw.1: |- ph


  assert |- ( A. x ph -> ph )

  proof
    wph
    wph
    vx
    wal
    sptruw.1
    a1i
end
