include "wceq.mm"
include "wrex.mm"
include "rexeq.mm"
include "rexbidv.mm"
include "bitrd.mm"

theorem rexeqbi1dv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume raleqd.1: |- ( A = B -> ( ph <-> ps ) )

  disjoint A x
  disjoint B x
  assert |- ( A = B -> ( E. x e. A ph <-> E. x e. B ps ) )

  proof
    cA
    cB
    wceq
    #
    wph
    vx
    cA
    wrex
    wph
    vx
    cB
    wrex
    wps
    vx
    cB
    wrex
    wph
    vx
    cA
    cB
    rexeq
    @0
    wph
    wps
    vx
    cB
    raleqd.1
    rexbidv
    bitrd
end
