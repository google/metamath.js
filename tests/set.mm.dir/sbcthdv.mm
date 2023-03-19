include "wal.mm"
include "wcel.mm"
include "wsbc.mm"
include "alrimiv.mm"
include "spsbc.mm"
include "mpan9.mm"

theorem sbcthdv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume sbcthdv.1: |- ( ph -> ps )

  disjoint ph x
  assert |- ( ( ph /\ A e. V ) -> [. A / x ]. ps )

  proof
    wph
    wps
    vx
    wal
    cA
    cV
    wcel
    wps
    vx
    cA
    wsbc
    wph
    wps
    vx
    sbcthdv.1
    alrimiv
    wps
    vx
    cA
    cV
    spsbc
    mpan9
end
