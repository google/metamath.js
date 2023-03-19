include "wcel.mm"
include "wral.mm"
include "wsbc.mm"
include "rgen.mm"
include "rspsbc.mm"
include "mpi.mm"

theorem sbcth2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume sbcth2.1: |- ( x e. B -> ph )

  disjoint B x
  assert |- ( A e. B -> [. A / x ]. ph )

  proof
    cA
    cB
    wcel
    wph
    vx
    cB
    wral
    wph
    vx
    cA
    wsbc
    wph
    vx
    cB
    sbcth2.1
    rgen
    wph
    vx
    cA
    cB
    rspsbc
    mpi
end
