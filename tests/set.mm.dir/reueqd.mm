include "wceq.mm"
include "wreu.mm"
include "reueq1.mm"
include "reubidv.mm"
include "bitrd.mm"

theorem reueqd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume raleqd.1: |- ( A = B -> ( ph <-> ps ) )

  disjoint A x
  disjoint B x
  assert |- ( A = B -> ( E! x e. A ph <-> E! x e. B ps ) )

  proof
    cA
    cB
    wceq
    #
    wph
    vx
    cA
    wreu
    wph
    vx
    cB
    wreu
    wps
    vx
    cB
    wreu
    wph
    vx
    cA
    cB
    reueq1
    @0
    wph
    wps
    vx
    cB
    raleqd.1
    reubidv
    bitrd
end
