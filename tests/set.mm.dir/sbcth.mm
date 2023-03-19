include "wcel.mm"
include "wal.mm"
include "wsbc.mm"
include "ax-gen.mm"
include "spsbc.mm"
include "mpi.mm"

theorem sbcth
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume sbcth.1: |- ph


  assert |- ( A e. V -> [. A / x ]. ph )

  proof
    cA
    cV
    wcel
    wph
    vx
    wal
    wph
    vx
    cA
    wsbc
    wph
    vx
    sbcth.1
    ax-gen
    wph
    vx
    cA
    cV
    spsbc
    mpi
end
