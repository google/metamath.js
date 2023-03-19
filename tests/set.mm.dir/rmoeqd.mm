include "wceq.mm"
include "wrmo.mm"
include "rmoeq1.mm"
include "rmobidv.mm"
include "bitrd.mm"

theorem rmoeqd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume raleqd.1: |- ( A = B -> ( ph <-> ps ) )

  disjoint A x
  disjoint B x
  assert |- ( A = B -> ( E* x e. A ph <-> E* x e. B ps ) )

  proof
    cA
    cB
    wceq
    #
    wph
    vx
    cA
    wrmo
    wph
    vx
    cB
    wrmo
    wps
    vx
    cB
    wrmo
    wph
    vx
    cA
    cB
    rmoeq1
    @0
    wph
    wps
    vx
    cB
    raleqd.1
    rmobidv
    bitrd
end
